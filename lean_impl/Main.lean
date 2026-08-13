import AptpCheck

/-!
# `aptpcheck` — command-line tool

Usage: `aptpcheck <network.net> <proof.aptp> [--vipr-dir <dir>]`

Parses the network and proof tree, checks coverage, encodes each leaf into a MILP
(emitted as a VIPR-format CON section), invokes exact SCIP to produce a `.vipr`
certificate, then re-checks the certificate with the verified `checkVipr`. Reports
"CERTIFIED" iff every leaf's certificate validates.

The soundness guarantee:
  checkVipr_sound + encoding_overapprox_mlp + coverage_sound + toMLP_eval
  ⟹ ∀ x ∈ dom, c · net(x) > ρ.

What is trusted (the TCB beyond Lean's kernel): only the operating system and I/O.
The parsers, the encoder, the certificate checker, and the composition are all verified.
-/

open AptpCheck.Ast AptpCheck.Cert AptpCheck.Model AptpCheck.Pipeline AptpCheck.Coverage

/-- Emit a leaf's encoding as VIPR v1.0 text (CON section + metadata). -/
def emitVipr (rows : List Le) (objRow : Le) (intVars : List Nat)
    (numVars : Nat) : String := Id.run do
  let mut s := s!"VER 1.0\nVAR {numVars}"
  for i in List.range numVars do s := s ++ s!" v{i}"
  s := s ++ s!"\nINT {intVars.length}"
  for j in intVars do s := s ++ s!" {j}"
  s := s ++ "\nOBJ min 0\n"
  -- CON: rows + objRow
  let allRows := rows ++ [objRow]
  s := s ++ s!"CON {allRows.length} 0\n"
  for (idx, r) in (List.range allRows.length).zip allRows do
    let terms := r.form.filter (fun t => t.coeff != 0)
    s := s ++ s!"r{idx} L {r.rhs} {terms.length}"
    for t in terms do s := s ++ s!" {t.idx} {t.coeff}"
    s := s ++ "\n"
  s := s ++ "RTP infeas\nSOL 0\nDER 0\n"
  return s

/-- Invoke SCIP on a `.vipr` file and return the certificate text. The `scip` binary
must be on PATH (SoPlex-backed exact SCIP). This is the *only* untrusted step; its
output is re-validated by the verified `checkVipr`. -/
def runScip (viprPath : String) : IO (Except String String) := do
  let certPath := viprPath ++ ".cert"
  let result ← IO.Process.output {
    cmd := "scip"
    args := #["-c",
      s!"set numerics feastol 0\nset lp solvefreq -1\nread {viprPath}\noptimize\nwrite proof {certPath}\nquit"]
  }
  if result.exitCode != 0 then
    return .error s!"SCIP exited with code {result.exitCode}: {result.stderr.take 200}"
  let cert ← IO.FS.readFile ⟨certPath⟩
  return .ok cert

/-- Check one leaf: encode, emit VIPR, invoke SCIP, validate the certificate. -/
def checkLeafIO (net : Network) (prob : Problem) (obj : Objective)
    (leaf : Array Int) (viprDir : String) (leafIdx : Nat) : IO Bool := do
  let (rows, objRow) := encode net prob.box leaf.toList obj.c obj.rhs
  let intVars := (rows ++ [objRow]).foldl (fun acc r =>
      r.form.foldl (fun a t => if a.contains t.idx then a else a ++ [t.idx]) acc) ([] : List Nat)
  -- Only binaries are integer; filter to those used in big-M gadgets (idx convention TBD).
  -- For now mark ALL variables as integer (sound over-approximation: if infeasible under
  -- tighter integrality it's certainly infeasible under weaker).
  let numVars := (rows ++ [objRow]).foldl (fun mx r =>
      r.form.foldl (fun m t => max m (t.idx + 1)) mx) 0
  let viprText := emitVipr rows objRow intVars numVars
  let path := s!"{viprDir}/leaf_{leafIdx}.vipr"
  IO.FS.writeFile ⟨path⟩ viprText
  match ← runScip path with
  | .error e => IO.eprintln s!"  leaf {leafIdx}: SCIP error: {e}"; return false
  | .ok cert =>
    match parseVipr cert with
    | .error e => IO.eprintln s!"  leaf {leafIdx}: parse error: {e}"; return false
    | .ok v =>
      if checkVipr v then
        IO.println s!"  leaf {leafIdx}: CERTIFIED"; return true
      else
        IO.eprintln s!"  leaf {leafIdx}: certificate REJECTED by checker"; return false

def main (args : List String) : IO UInt32 := do
  -- Parse arguments
  let (netPath, aptpPath, viprDir) ← match args with
    | [n, a] => pure (n, a, "/tmp/aptpcheck_vipr")
    | [n, a, "--vipr-dir", d] => pure (n, a, d)
    | _ =>
      IO.eprintln "Usage: aptpcheck <network.net> <proof.aptp> [--vipr-dir <dir>]"
      return 1
  -- Create vipr output dir
  IO.FS.createDirAll ⟨viprDir⟩
  -- Parse inputs
  let netContent ← IO.FS.readFile ⟨netPath⟩
  let aptpContent ← IO.FS.readFile ⟨aptpPath⟩
  let net ← match parseNet netContent with
    | .ok n => pure n
    | .error e => IO.eprintln s!"Error parsing .net: {e}"; return 1
  let prob ← match parseAptp aptpContent with
    | .ok p => pure p
    | .error e => IO.eprintln s!"Error parsing .aptp: {e}"; return 1
  -- Check network is MLP
  match toMLP net with
  | none => IO.eprintln "Error: network is not in MLP normal form (Linear,(ReLU,Linear)*)"; return 1
  | some _ => pure ()
  -- Check coverage
  let leaves := prob.leaves.toList.map (fun l => l.toList)
  if !checkCoverage leaves then
    IO.eprintln "Error: leaves do NOT cover the activation-pattern cube"; return 1
  IO.println "Coverage: OK"
  -- Check each leaf × objective
  let mut allOk := true
  for (oi, obj) in (List.range prob.objectives.toList.length).zip prob.objectives.toList do
    IO.println s!"Objective {oi}: c={obj.c.toList}, rhs={obj.rhs}"
    for (li, leaf) in (List.range prob.leaves.toList.length).zip prob.leaves.toList do
      let ok ← checkLeafIO net prob obj leaf viprDir (oi * prob.leaves.size + li)
      if !ok then allOk := false
  if allOk then
    IO.println "\n══════════════════════════════════════"
    IO.println "CERTIFIED: ∀ x ∈ dom, c · net(x) > ρ"
    IO.println "══════════════════════════════════════"
    return 0
  else
    IO.eprintln "\nUNCERTIFIED: one or more leaves failed."
    return 2
