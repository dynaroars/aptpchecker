import LeanVIPR

/-!
# `viprcheck` — re-check a VIPR result certificate

Usage:

* `viprcheck <certificate.vipr> [--proof-dir <dir>]`
* `viprcheck --native-precheck <certificate.vipr>`
* `viprcheck --native-mode <full|slice> <certificate.vipr>`
* `viprcheck --kernel-mode <full|reconstruct> <certificate.vipr>
    [--proof-dir <dir>]`

The normal mode parses a VIPR v1.0 file, emits the parsed certificate as Lean data,
and asks Lean's kernel to reduce the array-backed `checkVipr`, including
`SOL`, `{ sol }`, final objective-bound checking, and infeasibility results.
`RTP infeas` retains the optional reconstruction optimization. SCIP is not
invoked; the certificate file is the input.

`--native-precheck` executes the same Boolean checker as compiled code, but is only
an explicitly untrusted performance/preflight mode.

The checker is proved sound directly against the declarative VIPR proof system.

The generated theorem currently certifies the emitted certificate AST. Binding that
AST to the exact source bytes remains a frontend parser/runtime trust boundary.
-/

open LeanVIPR.Ast LeanVIPR.Cert LeanVIPR.Pipeline
open LeanVIPR.Cert.ViprChecker LeanVIPR.Ast.Vipr

inductive KernelMode where
  | full
  | reconstruct

def parseKernelMode? : String → Option KernelMode
  | "full" => some .full
  | "list" => some .full -- backwards-compatible name for complete replay
  | "reconstruct" => some .reconstruct
  | _ => none

def kernelModeName : KernelMode → String
  | .full => "full"
  | .reconstruct => "reconstruct"

def rtpKind : ViprRtp → String
  | .infeas => "infeas"
  | .range _ _ => "range"

def isAsm : ViprReason → Bool
  | .asm => true
  | _ => false
def isLin : ViprReason → Bool
  | .lin _ => true
  | .linWeak _ _ => true
  | _ => false
def isRnd : ViprReason → Bool
  | .rnd _ => true
  | _ => false
def isUns : ViprReason → Bool
  | .uns _ _ _ _ => true
  | _ => false
def isSol : ViprReason → Bool
  | .sol => true
  | _ => false

def countReason (ders : Array ViprDer) (p : ViprReason → Bool) : Nat :=
  ders.foldl (fun n d => if p d.reason then n + 1 else n) 0

def reportCertificate (path : String) (v : Vipr) : IO Unit := do
  IO.println s!"file: {path}"
  IO.println s!"VER {v.version}  RTP {rtpKind v.rtp}"
  IO.println s!"vars {v.varNames.size}  int {v.intVars.length}  con {v.numCon}  steps {v.ders.size}"
  IO.println (s!"reasons: asm×{countReason v.ders isAsm}  "
    ++ s!"lin×{countReason v.ders isLin}  rnd×{countReason v.ders isRnd}  "
    ++ s!"uns×{countReason v.ders isUns}  sol×{countReason v.ders isSol}")

def parseFile (path : String) : IO (Except String (String × Vipr)) := do
  let content ← IO.FS.readFile ⟨path⟩
  match parseVipr content with
  | .error e => return .error e
  | .ok v => return .ok (content, v)

def renderVipr (cert : Vipr) : String :=
  s!"({(repr cert).pretty 100000000} : Vipr)"

def emittedOptionRatDivision : String :=
  "private instance : HDiv (Option ℚ) Nat (Option ℚ) where\n"
  ++ "  hDiv q n := q.map (fun x => x / n)\n\n"

def viprReasonRefs : ViprReason → List Nat
  | .asm => []
  | .lin terms => terms.map Prod.fst
  | .linWeak bounds terms =>
      terms.map Prod.fst ++
        match bounds with
        | .global => []
        | .local localBounds => localBounds.map (·.rowIdx)
  | .rnd terms => terms.map Prod.fst
  | .uns i1 l1 i2 l2 => [i1, l1, i2, l2]
  | .sol => []

def mapWeakBounds (f : Nat → Nat) : ViprWeakBounds → ViprWeakBounds
  | .global => .global
  | .local bounds => .local (bounds.map fun bound => { bound with rowIdx := f bound.rowIdx })

def mapViprReason (f : Nat → Nat) : ViprReason → ViprReason
  | .asm => .asm
  | .lin terms => .lin (terms.map fun p => (f p.1, p.2))
  | .linWeak bounds terms =>
      .linWeak (mapWeakBounds f bounds) (terms.map fun p => (f p.1, p.2))
  | .rnd terms => .rnd (terms.map fun p => (f p.1, p.2))
  | .uns i1 l1 i2 l2 => .uns (f i1) (f l1) (f i2) (f l2)
  | .sol => .sol

def isLinWeak : ViprReason → Bool
  | .linWeak _ _ => true
  | _ => false

/-- Replace each incomplete `lin weak` reason with the ordinary linear combination
proposed by the completion algorithm. The ordinary checker still validates every
materialized combination, so this transformation is untrusted preprocessing. -/
def materializeWeakVipr (v : Vipr) : Vipr :=
  { v with
    ders := v.ders.mapIdx fun idx d =>
      match d.reason with
      | .linWeak bounds terms =>
          let comb := completeWeakComb v idx (derStated v d) bounds terms
          { d with reason := .lin (comb.map fun p => (p.2, p.1)) }
      | _ => d }

/-- Untrusted proof-producing slice. The generated reconstruction theorem separately
kernel-checks both the sliced replay and its row-subset relation to the original. -/
def sliceVipr (input : Vipr) : Vipr := Id.run do
  let v := materializeWeakVipr input
  if v.ders.isEmpty || v.cons.size != v.numCon then
    return v
  let ncon := v.numCon
  let nder := v.ders.size
  -- A range certificate retains every problem row so its checked solution witnesses
  -- and objective bounds describe exactly the original problem. Infeasibility can
  -- safely retain only the refuted row subset.
  let keepAllCon := match v.rtp with
    | .infeas => false
    | .range _ _ => true
  let mut keepCon := Array.replicate ncon keepAllCon
  let mut keepDer := Array.replicate nder false
  let mut todo : List Nat := [nder - 1]
  while !todo.isEmpty do
    let i := todo.headD 0
    todo := todo.tail
    if i < nder && !(keepDer.getD i false) then
      keepDer := keepDer.set! i true
      let d := v.ders.getD i default
      for ref in viprReasonRefs d.reason do
        if ref < ncon then
          keepCon := keepCon.setIfInBounds ref true
        else
          todo := (ref - ncon) :: todo
  let mut conRank := Array.replicate ncon 0
  let mut keptCon := 0
  for i in [:ncon] do
    conRank := conRank.set! i keptCon
    if keepCon.getD i false then keptCon := keptCon + 1
  let mut derRank := Array.replicate nder 0
  let mut keptDer := 0
  for i in [:nder] do
    derRank := derRank.set! i keptDer
    if keepDer.getD i false then keptDer := keptDer + 1
  let remap := fun ref =>
    if ref < ncon then conRank.getD ref 0
    else keptCon + derRank.getD (ref - ncon) 0
  let mut cons : Array ViprCon := #[]
  let mut numBounds := 0
  for i in [:ncon] do
    if keepCon.getD i false then
      let c := v.cons.getD i default
      cons := cons.push c
      if c.name.toList.head? == some 'B' then numBounds := numBounds + 1
  let mut ders : Array ViprDer := #[]
  for i in [:nder] do
    if keepDer.getD i false then
      let d := v.ders.getD i default
      ders := ders.push { d with reason := mapViprReason remap d.reason }
  return { v with numCon := keptCon, numBounds := numBounds, cons := cons, ders := ders }

def emitViprData (sourceText : String) (cert : Vipr) : String :=
  "import LeanVIPR.Pipeline.Vipr\n\n"
  ++ "set_option maxHeartbeats 0\n"
  ++ "set_option maxRecDepth 1000000\n\n"
  ++ "namespace LeanVIPR.Generated\n\n"
  ++ "open LeanVIPR.Ast\n\n"
  ++ emittedOptionRatDivision
  ++ s!"def sourceText : String := {String.quote sourceText}\n\n"
  ++ s!"def cert : Vipr := {renderVipr cert}\n\n"
  ++ "end LeanVIPR.Generated\n"

def emitViprReconstructionData (sourceText : String) (original sliced : Vipr) : String :=
  "import LeanVIPR.Pipeline.Vipr\n\n"
  ++ "set_option maxHeartbeats 0\n"
  ++ "set_option maxRecDepth 1000000\n\n"
  ++ "namespace LeanVIPR.Generated\n\n"
  ++ "open LeanVIPR.Ast\n\n"
  ++ emittedOptionRatDivision
  ++ s!"def sourceText : String := {String.quote sourceText}\n\n"
  ++ s!"def original : Vipr := {renderVipr original}\n\n"
  ++ s!"def sliced : Vipr := {renderVipr sliced}\n\n"
  ++ "end LeanVIPR.Generated\n"

def emitViprProof : String :=
  "import LeanVIPRGenerated.Data\n\n"
  ++ "import LeanVIPR.Cert.ViprCheckerSound\n\n"
  ++ "set_option maxHeartbeats 0\n"
  ++ "set_option maxRecDepth 1000000\n\n"
  ++ "namespace LeanVIPR.Generated\n\n"
  ++ "open LeanVIPR.Ast.Vipr LeanVIPR.Cert.ViprChecker\n\n"
  ++ "theorem accepted : checkVipr cert = true := by\n"
  ++ "  decide +kernel\n\n"
  ++ "theorem certified : Vipr.ClaimValid cert :=\n"
  ++ "  checkVipr_sound cert accepted\n\n"
  ++ "#print axioms certified\n\n"
  ++ "end LeanVIPR.Generated\n"

def emitViprReconstructionProof : String :=
  "import LeanVIPRGenerated.Data\n\n"
  ++ "import LeanVIPR.Cert.ViprCheckerSound\n\n"
  ++ "set_option maxHeartbeats 0\n"
  ++ "set_option maxRecDepth 1000000\n\n"
  ++ "namespace LeanVIPR.Generated\n\n"
  ++ "open LeanVIPR.Ast.Vipr LeanVIPR.Pipeline LeanVIPR.Cert.ViprChecker\n\n"
  ++ "theorem slicedInfeas : sliced.rtp = .infeas := by\n"
  ++ "  decide +kernel\n\n"
  ++ "theorem sameIntVars : sliced.intVars = original.intVars := by\n"
  ++ "  decide +kernel\n\n"
  ++ "theorem rowsSubset : ∀ c ∈ conSLes sliced, c ∈ conSLes original := by\n"
  ++ "  decide +kernel\n\n"
  ++ "theorem acceptedSlice : checkVipr sliced = true := by\n"
  ++ "  decide +kernel\n\n"
  ++ "theorem certified :\n"
  ++ "    ∀ a, Feasible original a → False :=\n"
  ++ "  checkViprInfeasibleSubset_sound original sliced slicedInfeas\n"
  ++ "    sameIntVars rowsSubset acceptedSlice\n\n"
  ++ "#print axioms certified\n\n"
  ++ "end LeanVIPR.Generated\n"

def generatedSourcePath (proofDir moduleName : String) : String :=
  s!"{proofDir}/LeanVIPRGenerated/{moduleName}.lean"

def generatedOleanPath (proofDir moduleName : String) : String :=
  s!"{proofDir}/LeanVIPRGenerated/{moduleName}.olean"

def runKernelModuleDirect (proofDir moduleName : String) : IO (Except String String) := do
  let sourcePath := generatedSourcePath proofDir moduleName
  let oleanPath := generatedOleanPath proofDir moduleName
  let inheritedLeanPath := (← IO.getEnv "LEAN_PATH").getD ""
  let localLeanPath :=
    if inheritedLeanPath.isEmpty then proofDir else proofDir ++ ":" ++ inheritedLeanPath
  let out ← IO.Process.output {
    cmd := "lean"
    args := #["-R", proofDir, "-o", oleanPath, sourcePath]
    env := #[("LEAN_PATH", some localLeanPath)] }
  if out.exitCode == 0 then
    return .ok (out.stdout ++ out.stderr)
  return .error (s!"kernel check failed in {moduleName} (exit {out.exitCode}):\n"
    ++ out.stdout ++ out.stderr)

def runKernelModulesDirect (proofDir : String) (moduleNames : List String) :
    IO (Except String String) := do
  let mut log := ""
  for moduleName in moduleNames do
    match ← runKernelModuleDirect proofDir moduleName with
    | .error e => return .error e
    | .ok out => log := log ++ out
  return .ok log

def runKernelModules (proofDir : String) (moduleNames : List String) :
    IO (Except String String) := do
  for moduleName in moduleNames do
    IO.println s!"kernel: {moduleName}"
  let lake := (← IO.getEnv "VIPR_LAKE").getD "lake"
  let self := (← IO.appPath).toString
  let out ← IO.Process.output {
    cmd := lake
    args := #["env", self, "--kernel-runner", proofDir] ++ moduleNames.toArray }
  if out.exitCode == 0 then
    return .ok (out.stdout ++ out.stderr)
  return .error s!"kernel runner exit {out.exitCode}:\n{out.stdout}{out.stderr}"

def checkFileNative (path : String) (useSlice : Bool := false) : IO UInt32 := do
  match ← parseFile path with
  | .error e =>
      IO.eprintln s!"parse error: {e}"
      return 1
  | .ok (_, v) =>
      reportCertificate path v
      let checked := if useSlice then sliceVipr v else v
      if useSlice then
        IO.println (s!"slice: {v.cons.size} → {checked.cons.size} constraints, "
          ++ s!"{v.ders.size} → {checked.ders.size} steps")
      let accepted := checkVipr checked
      if accepted then
        IO.println "NATIVE PRECHECK PASS  (verified array-backed checker; untrusted compiled/runtime result)"
        return 0
      else
        IO.eprintln "NATIVE PRECHECK REJECT  (result checker = false)"
        return 2

def reportInvalidReason (v : Vipr) (pool : CheckerPool)
    (original : ViprDer) (step : SStep) : IO Unit := do
  match step.reason with
  | .asm => IO.println "reason: asm"
  | .lin comb =>
      let resolved := resolveRefs pool comb
      let combined := scomb resolved
      IO.println s!"reason: lin ({comb.length} references)"
      IO.println s!"references-past: {referencesPastB pool step.reason}"
      IO.println s!"checkLin: {checkLin step.stated resolved}"
      IO.println s!"formEq: {formEq combined.form step.stated.form}"
      IO.println s!"suitLe: {suitLeB resolved}  suitGe: {suitGeB resolved}"
      IO.println s!"combined rhs: {combined.rhs}  stated rhs: {step.stated.rhs}"
      IO.println s!"combined form: {repr (normForm combined.form)}"
      IO.println s!"stated form: {repr (normForm step.stated.form)}"
      match original.reason with
      | .linWeak _ terms =>
          IO.println s!"weak base references: {terms.length}"
          for correction in comb.drop terms.length do
            IO.println s!"weak correction: multiplier {correction.1}, row {correction.2}"
            let row := poolRow pool correction.2
            IO.println s!"correction row: {row.sense} {row.rhs} {repr (normForm row.form)}"
      | _ => pure ()
  | .rnd comb =>
      IO.println s!"reason: rnd ({comb.length} references)"
      IO.println s!"references-past: {referencesPastB pool step.reason}"
      IO.println s!"rndCheck: {checkRnd v.intVars step.stated (resolveRefs pool comb)}"
  | .uns i1 l1 i2 l2 =>
      IO.println s!"reason: uns {i1} {l1} {i2} {l2}"
      IO.println s!"references-past: {referencesPastB pool step.reason}"
      IO.println s!"branch 1 dominates: {domSLe (poolRow pool i1) step.stated}"
      IO.println s!"branch 2 dominates: {domSLe (poolRow pool i2) step.stated}"
      IO.println s!"complementary bounds: {
        unsBoundsB v.intVars (poolRow pool l1) (poolRow pool l2)}"
  | .sol => IO.println "reason: sol"

/-- Diagnostic command: report the first rejected derivation without changing acceptance. -/
def debugFirstInvalid (path : String) : IO UInt32 := do
  match ← parseFile path with
  | .error e =>
      IO.eprintln s!"parse error: {e}"
      return 1
  | .ok (_, v) =>
      reportCertificate path v
      let steps := viprSteps v
      let mut pool := initialPool v
      let mut idx := 0
      for step in steps do
        let valid := stepValidB v pool step
        if !valid then
          IO.eprintln s!"first invalid derivation: step {idx}, VIPR row {v.cons.size + idx}"
          let original := v.ders.getD idx default
          IO.eprintln s!"name: {original.name}"
          reportInvalidReason v pool original step
          return 2
        pool := pool.push (entryOf pool step)
        idx := idx + 1
      IO.println "all derivation steps pass"
      IO.println s!"final result: {solSectionB v && finalValidB v pool.back?}"
      return 0

def checkFileKernel (path proofDir : String) (mode : KernelMode) : IO UInt32 := do
  match ← parseFile path with
  | .error e =>
      IO.eprintln s!"parse error: {e}"
      return 1
  | .ok (sourceText, v) =>
      reportCertificate path v
      let mut dataSource := ""
      let mut proofSource := ""
      let mut effectiveMode := mode
      match v.rtp with
      | .range _ _ =>
          match mode with
          | .full => pure ()
          | .reconstruct =>
              IO.println "range result: reconstruction is unavailable; using complete replay"
          effectiveMode := .full
          if !checkVipr v then
            IO.eprintln "REJECT  (native precheck found checkVipr = false)"
            return 2
          dataSource := emitViprData sourceText v
          proofSource := emitViprProof
      | .infeas =>
          match mode with
          | .full =>
            if !checkVipr v then
              IO.eprintln "REJECT  (native precheck found checkVipr = false)"
              return 2
            dataSource := emitViprData sourceText v
            proofSource := emitViprProof
          | .reconstruct =>
              let sliced := sliceVipr v
              if checkVipr sliced then
                IO.println (s!"slice: {v.cons.size} → {sliced.cons.size} constraints, "
                  ++ s!"{v.ders.size} → {sliced.ders.size} steps")
                dataSource := emitViprReconstructionData sourceText v sliced
                proofSource := emitViprReconstructionProof
              else if checkVipr v then
                IO.println "slice precheck failed; falling back to complete replay"
                effectiveMode := .full
                dataSource := emitViprData sourceText v
                proofSource := emitViprProof
              else
                IO.eprintln "REJECT  (native prechecks found no valid replay)"
                return 2
      let generatedDir := s!"{proofDir}/LeanVIPRGenerated"
      IO.FS.createDirAll ⟨generatedDir⟩
      IO.FS.writeFile ⟨generatedSourcePath proofDir "Data"⟩ dataSource
      IO.FS.writeFile ⟨generatedSourcePath proofDir "Proof"⟩ proofSource
      match ← runKernelModules proofDir ["Data", "Proof"] with
      | .error e =>
          IO.eprintln e
          return 2
      | .ok log =>
          if !log.isEmpty then IO.println log
          IO.println (s!"ACCEPT  (kernel-checked {kernelModeName effectiveMode}; "
            ++ "theorem LeanVIPR.Generated.certified)")
          IO.println s!"proof artifact: {generatedSourcePath proofDir "Proof"}"
          return 0

def runKernelMode (modeText path proofDir : String) : IO UInt32 := do
  match parseKernelMode? modeText with
  | none =>
      IO.eprintln s!"unknown kernel mode: {modeText}"
      return 1
  | some mode => checkFileKernel path proofDir mode

def main (args : List String) : IO UInt32 := do
  match args with
  | "--kernel-runner" :: proofDir :: moduleNames =>
      match ← runKernelModulesDirect proofDir moduleNames with
      | .error e =>
          IO.eprintln e
          return 2
      | .ok log =>
          if !log.isEmpty then IO.println log
          return 0
  | ["--native-precheck", path] => checkFileNative path
  | ["--native-mode", "full", path] => checkFileNative path false
  | ["--native-mode", "slice", path] => checkFileNative path true
  | ["--debug-first-invalid", path] => debugFirstInvalid path
  | ["--kernel-mode", mode, path] =>
      runKernelMode mode path s!"/tmp/viprcheck_{mode}"
  | ["--kernel-mode", mode, path, "--proof-dir", proofDir] =>
      runKernelMode mode path proofDir
  | [path] => checkFileKernel path "/tmp/viprcheck_proof" .reconstruct
  | [path, "--proof-dir", proofDir] => checkFileKernel path proofDir .reconstruct
  | _ =>
      IO.eprintln "Usage: viprcheck <certificate.vipr> [--proof-dir <dir>]"
      IO.eprintln "       viprcheck --native-precheck <certificate.vipr>"
      IO.eprintln "       viprcheck --native-mode <full|slice> <certificate.vipr>"
      IO.eprintln "       viprcheck --debug-first-invalid <certificate.vipr>"
      IO.eprintln "       viprcheck --kernel-mode <full|reconstruct> <certificate.vipr>"
      return 1
