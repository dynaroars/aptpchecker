import LeanVIPR

/-!
Small kernel-reduced smoke tests for VIPR checking.

The valid examples exercise both objective directions and `{ sol }`.  The
forged examples mirror the two failure shapes used in the VIPR checker
literature: an invalid `{ sol }` direction and a missing final dual-bound row.
-/

open LeanVIPR.Ast LeanVIPR.Cert LeanVIPR.Ast.Vipr
open LeanVIPR.Cert.ViprChecker
open LeanVIPR.Cert.ViprComplexity

def xForm : LinForm := [⟨0, 1⟩]

def minRangeCert : Vipr :=
  { version := "1.0"
    varNames := #["x"]
    intVars := []
    objSense := "min"
    objTerms := [(0, 1)]
    numCon := 2
    numBounds := 0
    cons := #[
      { name := "C0", sense := 'G', rhs := 0, form := xForm, usesObj := false },
      { name := "C1", sense := 'L', rhs := 2, form := xForm, usesObj := false }]
    rtp := .range (some 0) (some 0)
    numSol := 1
    sols := #[("opt", [(0, 0)])]
    ders := #[
      { name := "D0", sense := 'L', rhs := 0, form := [], usesObj := true
        reason := .sol, idx := -1 },
      { name := "D1", sense := 'G', rhs := 0, form := [], usesObj := true
        reason := .lin [(0, 1)], idx := -1 }] }

def maxRangeCert : Vipr :=
  { version := "1.0"
    varNames := #["x"]
    intVars := []
    objSense := "max"
    objTerms := [(0, 1)]
    numCon := 2
    numBounds := 0
    cons := #[
      { name := "C0", sense := 'L', rhs := 1, form := xForm, usesObj := false },
      { name := "C1", sense := 'G', rhs := 0, form := xForm, usesObj := false }]
    rtp := .range (some 1) (some 1)
    numSol := 1
    sols := #[("opt", [(0, 1)])]
    ders := #[
      { name := "D0", sense := 'G', rhs := 1, form := [], usesObj := true
        reason := .sol, idx := -1 },
      { name := "D1", sense := 'L', rhs := 1, form := [], usesObj := true
        reason := .lin [(0, 1)], idx := -1 }] }

def simpleInfeasCert : Vipr :=
  { version := "1.0"
    varNames := #["x"]
    intVars := []
    objSense := "min"
    objTerms := []
    numCon := 2
    numBounds := 0
    cons := #[
      { name := "C0", sense := 'L', rhs := 0, form := xForm, usesObj := false },
      { name := "C1", sense := 'G', rhs := 1, form := xForm, usesObj := false }]
    rtp := .infeas
    numSol := 0
    sols := #[]
    ders := #[
      { name := "D0", sense := 'L', rhs := -1, form := [], usesObj := false
        reason := .lin [(0, 1), (1, -1)], idx := -1 }] }

def forgedSolDirection : Vipr :=
  { version := "1.0"
    varNames := #["x", "y"]
    intVars := [0, 1]
    objSense := "max"
    objTerms := [(0, 1), (1, 1)]
    numCon := 4
    numBounds := 4
    cons := #[
      { name := "C1", sense := 'L', rhs := 1, form := [⟨0, 1⟩], usesObj := false },
      { name := "C2", sense := 'L', rhs := 1, form := [⟨1, 1⟩], usesObj := false },
      { name := "B1", sense := 'G', rhs := 0, form := [⟨0, 1⟩], usesObj := false },
      { name := "B2", sense := 'G', rhs := 0, form := [⟨1, 1⟩], usesObj := false }]
    rtp := .range (some 1) (some 1)
    numSol := 1
    sols := #[("opt", [(1, 1)])]
    ders := #[
      { name := "C3", sense := 'L', rhs := 1, form := [], usesObj := true
        reason := .sol, idx := -1 }] }

def forgedMissingFinal : Vipr :=
  { version := "1.0"
    varNames := #["x", "y"]
    intVars := [0, 1]
    objSense := "max"
    objTerms := [(0, 1), (1, 1)]
    numCon := 4
    numBounds := 4
    cons := #[
      { name := "C1", sense := 'L', rhs := 1 / 2, form := [⟨0, 1⟩], usesObj := false },
      { name := "C2", sense := 'L', rhs := 1 / 2, form := [⟨1, 1⟩], usesObj := false },
      { name := "B1", sense := 'G', rhs := 1 / 3, form := [⟨0, 1⟩], usesObj := false },
      { name := "B2", sense := 'G', rhs := 1 / 3, form := [⟨1, 1⟩], usesObj := false }]
    rtp := .range none (some 0)
    numSol := 0
    sols := #[]
    ders := #[] }

example : checkVipr minRangeCert = true := by decide +kernel
example : checkVipr maxRangeCert = true := by decide +kernel
example : checkVipr simpleInfeasCert = true := by decide +kernel
example : checkVipr forgedSolDirection = false := by decide +kernel
example : checkVipr forgedMissingFinal = false := by decide +kernel

example : Vipr.ClaimValid minRangeCert :=
  checkVipr_sound minRangeCert (by decide +kernel)

example : Vipr.ClaimValid maxRangeCert :=
  checkVipr_sound maxRangeCert (by decide +kernel)

/-! The structural cost profile preserves the checker result and accounts for
both infeasibility and range certificates. -/

example : (checkViprProfiled minRangeCert).1 = true := by decide +kernel
example : (checkerWorkUpper minRangeCert).ruleChecks = 2 := by decide +kernel
example : 0 < (checkerWorkUpper minRangeCert).solutionInputCells := by decide +kernel

example : (checkViprProfiled simpleInfeasCert).1 = true := by decide +kernel
example : (checkerWorkUpper simpleInfeasCert).ruleChecks = 1 := by decide +kernel
example : (checkerWorkUpper simpleInfeasCert).solutionInputCells = 0 := by decide +kernel

example := checkVipr_structural_cost minRangeCert
example := checkVipr_structural_cost simpleInfeasCert
