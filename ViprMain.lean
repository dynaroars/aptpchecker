import ViprCheck

/-!
# `viprcheck` — re-check a VIPR result certificate

Usage:

* `viprcheck <certificate.vipr> [--proof-dir <dir>]`
* `viprcheck --native-precheck <certificate.vipr>`
* `viprcheck --kernel-mode <list|reconstruct> <certificate.vipr>
    [--proof-dir <dir>]`

The normal mode parses a VIPR v1.0 file, emits the parsed certificate as Lean data,
and asks Lean's kernel to reduce the relevant Boolean checker. `RTP range` uses
`checkViprResult`, including `SOL`, `{ sol }`, and final objective-bound checking.
`RTP infeas` retains the optional reconstruction optimization. SCIP is not invoked;
the certificate file is the input.

`--native-precheck` executes the same Boolean checker as compiled code, but is only
an explicitly untrusted performance/preflight mode.

The generated theorem currently certifies the emitted certificate AST. Binding that
AST to the exact source bytes remains a frontend parser/runtime trust boundary.
-/

open ViprCheck.Ast ViprCheck.Pipeline

inductive KernelMode where
  | list
  | reconstruct

def parseKernelMode? : String → Option KernelMode
  | "list" => some .list
  | "reconstruct" => some .reconstruct
  | _ => none

def kernelModeName : KernelMode → String
  | .list => "list"
  | .reconstruct => "reconstruct"

def rtpKind : ViprRtp → String
  | .infeas => "infeas"
  | .range _ _ => "range"

def isAsm : ViprReason → Bool
  | .asm => true
  | _ => false
def isLin : ViprReason → Bool
  | .lin _ => true
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

def viprReasonRefs : ViprReason → List Nat
  | .asm => []
  | .lin terms => terms.map Prod.fst
  | .rnd terms => terms.map Prod.fst
  | .uns i1 l1 i2 l2 => [i1, l1, i2, l2]
  | .sol => []

def mapViprReason (f : Nat → Nat) : ViprReason → ViprReason
  | .asm => .asm
  | .lin terms => .lin (terms.map fun p => (f p.1, p.2))
  | .rnd terms => .rnd (terms.map fun p => (f p.1, p.2))
  | .uns i1 l1 i2 l2 => .uns (f i1) (f l1) (f i2) (f l2)
  | .sol => .sol

/-- Untrusted proof-producing slice. The generated reconstruction theorem separately
kernel-checks both the sliced replay and its row-subset relation to the original. -/
def sliceVipr (v : Vipr) : Vipr := Id.run do
  if v.ders.isEmpty || v.cons.size != v.numCon then return v
  let ncon := v.numCon
  let nder := v.ders.size
  let mut keepCon := Array.replicate ncon false
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
  "import ViprCheck.Pipeline.Vipr\n\n"
  ++ "set_option maxHeartbeats 0\n"
  ++ "set_option maxRecDepth 1000000\n\n"
  ++ "namespace ViprCheck.Generated\n\n"
  ++ "open ViprCheck.Ast\n\n"
  ++ s!"def sourceText : String := {String.quote sourceText}\n\n"
  ++ s!"def cert : Vipr := {renderVipr cert}\n\n"
  ++ "end ViprCheck.Generated\n"

def emitViprReconstructionData (sourceText : String) (original sliced : Vipr) : String :=
  "import ViprCheck.Pipeline.Vipr\n\n"
  ++ "set_option maxHeartbeats 0\n"
  ++ "set_option maxRecDepth 1000000\n\n"
  ++ "namespace ViprCheck.Generated\n\n"
  ++ "open ViprCheck.Ast\n\n"
  ++ s!"def sourceText : String := {String.quote sourceText}\n\n"
  ++ s!"def original : Vipr := {renderVipr original}\n\n"
  ++ s!"def sliced : Vipr := {renderVipr sliced}\n\n"
  ++ "end ViprCheck.Generated\n"

def emitViprProof : String :=
  "import ViprCheckGenerated.Data\n\n"
  ++ "set_option maxHeartbeats 0\n"
  ++ "set_option maxRecDepth 1000000\n\n"
  ++ "namespace ViprCheck.Generated\n\n"
  ++ "open ViprCheck.Cert ViprCheck.Pipeline\n\n"
  ++ "theorem accepted : checkSem cert = true := by\n"
  ++ "  decide +kernel\n\n"
  ++ "theorem certified :\n"
  ++ "    ∀ a, (∀ j ∈ cert.intVars, IsIntVal (a j)) →\n"
  ++ "      (∀ c ∈ conSLes cert, SLe.sat c a) → False :=\n"
  ++ "  checkSem_sound cert accepted\n\n"
  ++ "#print axioms certified\n\n"
  ++ "end ViprCheck.Generated\n"

def emitViprResultProof : String :=
  "import ViprCheckGenerated.Data\n"
  ++ "import ViprCheck.Cert.ViprResultSound\n\n"
  ++ "set_option maxHeartbeats 0\n"
  ++ "set_option maxRecDepth 1000000\n\n"
  ++ "namespace ViprCheck.Generated\n\n"
  ++ "open ViprCheck.Cert.ViprResult\n\n"
  ++ "theorem accepted : checkViprResult cert = true := by\n"
  ++ "  decide +kernel\n\n"
  ++ "theorem certified : ResultCorrect cert :=\n"
  ++ "  checkViprResult_sound cert accepted\n\n"
  ++ "#print axioms certified\n\n"
  ++ "end ViprCheck.Generated\n"

def emitViprReconstructionProof : String :=
  "import ViprCheckGenerated.Data\n\n"
  ++ "set_option maxHeartbeats 0\n"
  ++ "set_option maxRecDepth 1000000\n\n"
  ++ "namespace ViprCheck.Generated\n\n"
  ++ "open ViprCheck.Cert ViprCheck.Pipeline\n\n"
  ++ "theorem sameIntVars : sliced.intVars = original.intVars := by\n"
  ++ "  decide +kernel\n\n"
  ++ "theorem rowsSubset : ∀ c ∈ conSLes sliced, c ∈ conSLes original := by\n"
  ++ "  decide +kernel\n\n"
  ++ "theorem acceptedSlice : checkSem sliced = true := by\n"
  ++ "  decide +kernel\n\n"
  ++ "theorem certified :\n"
  ++ "    ∀ a, (∀ j ∈ original.intVars, IsIntVal (a j)) →\n"
  ++ "      (∀ c ∈ conSLes original, SLe.sat c a) → False :=\n"
  ++ "  checkSem_subset_sound original sliced sameIntVars rowsSubset acceptedSlice\n\n"
  ++ "#print axioms certified\n\n"
  ++ "end ViprCheck.Generated\n"

def generatedSourcePath (proofDir moduleName : String) : String :=
  s!"{proofDir}/ViprCheckGenerated/{moduleName}.lean"

def generatedOleanPath (proofDir moduleName : String) : String :=
  s!"{proofDir}/ViprCheckGenerated/{moduleName}.olean"

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

def checkFileNative (path : String) : IO UInt32 := do
  match ← parseFile path with
  | .error e =>
      IO.eprintln s!"parse error: {e}"
      return 1
  | .ok (_, v) =>
      reportCertificate path v
      let accepted :=
        match v.rtp with
        | .infeas => checkSem v
        | .range _ _ => ViprCheck.Cert.ViprResult.checkViprResult v
      if accepted then
        IO.println "NATIVE PRECHECK PASS  (untrusted compiled/runtime result)"
        return 0
      else
        IO.eprintln "NATIVE PRECHECK REJECT  (result checker = false)"
        return 2

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
          | .list => pure ()
          | .reconstruct =>
              IO.println "range result: reconstruction is unavailable; using complete list replay"
          effectiveMode := .list
          if !ViprCheck.Cert.ViprResult.checkViprResult v then
            IO.eprintln "REJECT  (native precheck found checkViprResult = false)"
            return 2
          dataSource := emitViprData sourceText v
          proofSource := emitViprResultProof
      | .infeas =>
          match mode with
          | .list =>
            if !checkSem v then
              IO.eprintln "REJECT  (native precheck found checkSem = false)"
              return 2
            dataSource := emitViprData sourceText v
            proofSource := emitViprProof
          | .reconstruct =>
              let sliced := sliceVipr v
              if checkSem sliced then
                IO.println (s!"slice: {v.cons.size} → {sliced.cons.size} constraints, "
                  ++ s!"{v.ders.size} → {sliced.ders.size} steps")
                dataSource := emitViprReconstructionData sourceText v sliced
                proofSource := emitViprReconstructionProof
              else if checkSem v then
                IO.println "slice precheck failed; falling back to complete list replay"
                effectiveMode := .list
                dataSource := emitViprData sourceText v
                proofSource := emitViprProof
              else
                IO.eprintln "REJECT  (native prechecks found no valid replay)"
                return 2
      let generatedDir := s!"{proofDir}/ViprCheckGenerated"
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
            ++ "theorem ViprCheck.Generated.certified)")
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
  | ["--kernel-mode", mode, path] =>
      runKernelMode mode path s!"/tmp/viprcheck_{mode}"
  | ["--kernel-mode", mode, path, "--proof-dir", proofDir] =>
      runKernelMode mode path proofDir
  | [path] => checkFileKernel path "/tmp/viprcheck_proof" .reconstruct
  | [path, "--proof-dir", proofDir] => checkFileKernel path proofDir .reconstruct
  | _ =>
      IO.eprintln "Usage: viprcheck <certificate.vipr> [--proof-dir <dir>]"
      IO.eprintln "       viprcheck --native-precheck <certificate.vipr>"
      IO.eprintln "       viprcheck --kernel-mode <list|reconstruct> <certificate.vipr>"
      return 1
