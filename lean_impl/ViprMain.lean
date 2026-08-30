import AptpCheck

/-!
# `viprcheck` — re-check a VIPR infeasibility certificate

Usage: `viprcheck <certificate.vipr>`

Parses a VIPR v1.0 file and runs the verified checker `checkSem`. Prints `ACCEPT`
iff `checkSem` returns true. Soundness: `checkSem_sound` (axiom-clean). SCIP is
not invoked; the certificate file is the input. Trusted beyond the kernel: OS/I/O.
-/

open AptpCheck.Ast AptpCheck.Pipeline

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

def checkFile (path : String) : IO UInt32 := do
  let content ← IO.FS.readFile ⟨path⟩
  match parseVipr content with
  | .error e =>
    IO.eprintln s!"parse error: {e}"
    return 1
  | .ok v =>
    IO.println s!"file: {path}"
    IO.println s!"VER {v.version}  RTP {rtpKind v.rtp}"
    IO.println s!"vars {v.varNames.size}  int {v.intVars.length}  con {v.numCon}  steps {v.ders.size}"
    IO.println s!"reasons: asm×{countReason v.ders isAsm}  lin×{countReason v.ders isLin}  rnd×{countReason v.ders isRnd}  uns×{countReason v.ders isUns}  sol×{countReason v.ders isSol}"
    if checkSem v then
      IO.println "ACCEPT  (checkSem = true; CON rows infeasible over declared integers)"
      return 0
    else
      IO.eprintln "REJECT  (checkSem = false)"
      return 2

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] => checkFile path
  | _ =>
    IO.eprintln "Usage: viprcheck <certificate.vipr>"
    return 1
