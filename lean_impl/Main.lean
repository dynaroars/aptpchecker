import AptpCheck

/-!
# `aptpcheck` — command-line tool

Usage: `aptpcheck <network.net> <proof.aptp> [--vipr-dir <dir>]`
Env:   `APTP_SCIP` — path to the exact SCIP binary (default `scip`).

Pipeline: parse `.net` + `.aptp` → check coverage → for each leaf, encode a MILP,
write it as MPS with **exact rational** coefficients (only the ReLU binaries declared
integer), run **official exact SCIP** to produce a VIPR certificate, then re-check the
certificate with the verified `checkSem`. Reports CERTIFIED iff every leaf validates.

Trusted base beyond Lean's kernel: the OS + I/O. SCIP is untrusted (its certificate is
re-checked); a SCIP bug can only cause a spurious UNCERTIFIED, never a false CERTIFIED.
-/

open AptpCheck.Ast AptpCheck.Cert AptpCheck.Model AptpCheck.Pipeline AptpCheck.Coverage

/-- Format an exact rational as `num` or `num/den` (SCIP's exact MPS reader accepts both). -/
def fmtQ (q : ℚ) : String := if q.den == 1 then toString q.num else s!"{q.num}/{q.den}"

/-- Emit the leaf MILP `{rows} ∪ {objRow}` as MPS with exact coefficients. Only ids in
`binIds` are integer; every other variable is free (the box/affine rows bound them). -/
def emitMPS (rows : List Le) (objRow : Le) (binIds : List Nat) (numVars : Nat) : String := Id.run do
  let allRows := rows ++ [objRow]
  let n := allRows.length
  let coeffAt : Nat → Nat → ℚ := fun i v =>
    ((allRows.getD i ⟨[], 0⟩).form.filter (fun t => t.idx == v)).foldl (fun s t => s + t.coeff) 0
  let colEntries : Nat → List (Nat × ℚ) := fun v =>
    (List.range n).foldr (fun i acc => let c := coeffAt i v; if c == 0 then acc else (i, c) :: acc) []
  let emitCol : Nat → String := fun v =>
    (colEntries v).foldl (fun s p => s ++ s!"    V{v}  R{p.1}  {fmtQ p.2}\n") ""
  let mut s := "NAME          leaf\nROWS\n N  obj\n"
  for i in List.range n do s := s ++ s!" L  R{i}\n"
  s := s ++ "COLUMNS\n"
  for v in List.range numVars do
    if !binIds.contains v then s := s ++ emitCol v
  if !binIds.isEmpty then
    s := s ++ "    MK1  'MARKER'  'INTORG'\n"
    for v in binIds do s := s ++ emitCol v
    s := s ++ "    MK2  'MARKER'  'INTEND'\n"
  s := s ++ "RHS\n"
  for i in List.range n do s := s ++ s!"    rhs  R{i}  {fmtQ (allRows.getD i ⟨[], 0⟩).rhs}\n"
  s := s ++ "BOUNDS\n"
  for v in List.range numVars do
    if binIds.contains v then s := s ++ s!" LI BND  V{v}  0\n UI BND  V{v}  1\n"
    else s := s ++ s!" FR BND  V{v}\n"
  s := s ++ "ENDATA\n"
  return s

/-- Run exact SCIP on an MPS problem, producing a VIPR certificate. This is the only
untrusted step; its output is re-validated by `checkSem`. -/
def runScip (mpsPath certPath : String) : IO (Except String (String × String)) := do
  let scip := (← IO.getEnv "APTP_SCIP").getD "scip"
  let out ← IO.Process.output {
    cmd := scip
    args := #["-c", "set exact enable TRUE",
              "-c", "set presolving maxrounds 0",
              "-c", "set separating maxrounds 0", "-c", "set separating maxroundsroot 0",
              "-c", s!"set certificate filename {certPath}",
              "-c", s!"read {mpsPath}", "-c", "optimize", "-c", "quit"] }
  if out.exitCode != 0 then
    return .error s!"SCIP exit {out.exitCode}: {out.stderr.take 300}"
  let cert ← (do try pure (some (← IO.FS.readFile ⟨certPath⟩)) catch _ => pure none)
  match cert with
  | some c => return .ok (out.stdout, c)
  | none => return .error "SCIP produced no certificate file"

/-- Check one leaf: encode → MPS → SCIP → parse → `checkSem`. -/
def checkLeafIO (net : Network) (prob : Problem) (obj : Objective)
    (leaf : Array Int) (viprDir : String) (leafIdx : Nat) : IO Bool := do
  -- Encode the leaf with the verified leaf-aware encoder `encFold` (the one the
  -- soundness theorems `encFold_overapprox` / `certified_sound_network_fold` are about):
  -- it folds sign-fixed neurons (no binary) and only puts a big-M switch on genuinely
  -- unstable ones, giving a small MILP that exact SCIP proves with a complete certificate.
  let (rows, objRow, binIds) ← match encodeVerified net prob.box leaf.toList obj.c obj.rhs with
    | some t => pure t
    | none => IO.eprintln s!"  leaf {leafIdx}: not an MLP"; return false
  let numVars := (rows ++ [objRow]).foldl (fun mx r =>
      r.form.foldl (fun m t => max m (t.idx + 1)) mx) 0
  let mps := emitMPS rows objRow binIds numVars
  let mpsPath := s!"{viprDir}/leaf_{leafIdx}.mps"
  let certPath := s!"{viprDir}/leaf_{leafIdx}.vipr"
  IO.FS.writeFile ⟨mpsPath⟩ mps
  match ← runScip mpsPath certPath with
  | .error e => IO.eprintln s!"  leaf {leafIdx}: {e}"; return false
  | .ok (_log, cert) =>
    match parseVipr cert with
    | .error e => IO.eprintln s!"  leaf {leafIdx}: parse error: {e}"; return false
    | .ok v =>
      if checkSem v then
        IO.println s!"  leaf {leafIdx}: CERTIFIED (verified checkSem accepts SCIP's certificate)"
        return true
      else
        IO.eprintln s!"  leaf {leafIdx}: checkSem REJECTED the certificate"; return false

def main (args : List String) : IO UInt32 := do
  let (netPath, aptpPath, viprDir) ← match args with
    | [n, a] => pure (n, a, "/tmp/aptpcheck_vipr")
    | [n, a, "--vipr-dir", d] => pure (n, a, d)
    | _ => IO.eprintln "Usage: aptpcheck <network.net> <proof.aptp> [--vipr-dir <dir>]"; return 1
  IO.FS.createDirAll ⟨viprDir⟩
  let net ← match parseNet (← IO.FS.readFile ⟨netPath⟩) with
    | .ok n => pure n | .error e => IO.eprintln s!"Error parsing .net: {e}"; return 1
  let prob ← match parseAptp (← IO.FS.readFile ⟨aptpPath⟩) with
    | .ok p => pure p | .error e => IO.eprintln s!"Error parsing .aptp: {e}"; return 1
  match toMLP net with
  | none => IO.eprintln "Error: network is not in MLP normal form"; return 1
  | some _ => pure ()
  let leaves := prob.leaves.toList.map (fun l => l.toList)
  if !checkCoverage leaves then IO.eprintln "Error: leaves do NOT cover the cube"; return 1
  IO.println "Coverage: OK (leaves tile the activation-pattern cube)"
  let mut allOk := true
  for (oi, obj) in (List.range prob.objectives.toList.length).zip prob.objectives.toList do
    IO.println s!"Objective {oi}: c={obj.c.toList}, rhs={obj.rhs}"
    for (li, leaf) in (List.range prob.leaves.toList.length).zip prob.leaves.toList do
      let ok ← checkLeafIO net prob obj leaf viprDir (oi * prob.leaves.size + li)
      if !ok then allOk := false
  if allOk then
    IO.println "\nCERTIFIED: ∀ x ∈ dom, c · net(x) > ρ"
    return 0
  else
    IO.eprintln "\nUNCERTIFIED: one or more leaves failed."
    return 2
