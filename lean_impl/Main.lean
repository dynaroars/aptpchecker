import AptpCheck

/-- CLI entry point (scaffold). The verified pipeline is being built up module by
module; see DESIGN.md for the roadmap. -/
def main (_args : List String) : IO Unit := do
  IO.println "AptpCheck — a formally-verified APTP proof checker (Lean 4)."
  IO.println "Scaffold build OK. See DESIGN.md for the roadmap."
