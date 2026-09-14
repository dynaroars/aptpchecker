import LeanVIPR.Cert.ViprClaimSound

/-!
# Array-backed VIPR checker

This module implements the production VIPR checker:

* storing replay entries in an `Array`;
* fusing step validation and replay into one pass;
* computing each linear combination once per rule check.
-/

namespace LeanVIPR.Cert.ViprChecker

open LeanVIPR.Ast LeanVIPR.Cert LeanVIPR.Pipeline
open LeanVIPR.Ast.Vipr

abbrev CheckerEntry := SLe × SAsm
abbrev CheckerPool := Array CheckerEntry

@[inline] def poolEntry (pool : CheckerPool) (i : Nat) : CheckerEntry :=
  pool.getD i sdflt

@[inline] def poolRow (pool : CheckerPool) (i : Nat) : SLe :=
  (poolEntry pool i).1

@[inline] def poolAsm (pool : CheckerPool) (i : Nat) : SAsm :=
  (poolEntry pool i).2

def resolveRefs (pool : CheckerPool) (comb : List (ℚ × Nat)) : List (ℚ × SLe) :=
  comb.map fun p => (p.1, poolRow pool p.2)

def collectReferencedAsms (pool : CheckerPool) : List (ℚ × Nat) → SAsm
  | [] => ∅
  | p :: ps => poolAsm pool p.2 ∪ collectReferencedAsms pool ps

def entryOf (pool : CheckerPool) (s : SStep) : CheckerEntry :=
  match s.reason with
  | .asm => (s.stated, {s.stated})
  | .lin comb => (s.stated, collectReferencedAsms pool comb)
  | .rnd comb => (s.stated, collectReferencedAsms pool comb)
  | .uns i1 l1 i2 l2 =>
      (s.stated, (poolAsm pool i1).erase (poolRow pool l1) ∪
        (poolAsm pool i2).erase (poolRow pool l2))
  | .sol => (s.stated, ∅)

def linAbsurdB (cs : List (ℚ × SLe)) (combined : Le) : Bool :=
  (suitLeB cs && formIsZero combined.form && decide (combined.rhs < 0)) ||
  (suitGeB cs && formIsZero combined.form && decide (0 < combined.rhs))

def checkLin (stated : SLe) (cs : List (ℚ × SLe)) : Bool :=
  let combined := scomb cs
  linAbsurdB cs combined ||
  (formEq combined.form stated.form &&
    (if stated.sense = 'L' then suitLeB cs && decide (combined.rhs ≤ stated.rhs)
     else if stated.sense = 'G' then suitGeB cs && decide (stated.rhs ≤ combined.rhs)
     else false))

def checkRnd (intVars : List Nat) (stated : SLe) (cs : List (ℚ × SLe)) : Bool :=
  let combined := scomb cs
  formEq combined.form stated.form && formIntB intVars combined.form &&
  (if stated.sense = 'L' then
      suitLeB cs && decide (((⌊combined.rhs⌋ : ℤ) : ℚ) ≤ stated.rhs)
   else if stated.sense = 'G' then
      suitGeB cs && decide (stated.rhs ≤ ((⌈combined.rhs⌉ : ℤ) : ℚ))
   else false)

def referencesPastB (pool : CheckerPool) : SReason → Bool
  | .asm => true
  | .lin comb => comb.all fun p => decide (p.2 < pool.size)
  | .rnd comb => comb.all fun p => decide (p.2 < pool.size)
  | .uns i1 l1 i2 l2 =>
      decide (i1 < pool.size) && decide (l1 < pool.size) &&
      decide (i2 < pool.size) && decide (l2 < pool.size)
  | .sol => true

def stepValidB (v : Vipr) (pool : CheckerPool) (s : SStep) : Bool :=
  referencesPastB pool s.reason &&
  match s.reason with
  | .asm => true
  | .lin comb => checkLin s.stated (resolveRefs pool comb)
  | .rnd comb => checkRnd v.intVars s.stated (resolveRefs pool comb)
  | .uns i1 l1 i2 l2 =>
      domSLe (poolRow pool i1) s.stated &&
      domSLe (poolRow pool i2) s.stated &&
      unsBoundsB v.intVars (poolRow pool l1) (poolRow pool l2)
  | .sol => solReasonB v s.stated

def initialPool (v : Vipr) : CheckerPool :=
  v.cons.map fun c => (conToSLe v c, (∅ : SAsm))

def replaySteps? (v : Vipr) (pool : CheckerPool) : List SStep → Option CheckerPool
  | [] => some pool
  | s :: ss =>
      if stepValidB v pool s then
        replaySteps? v (pool.push (entryOf pool s)) ss
      else
        none

/-- `none` means that a step failed. `some last?` means replay succeeded, with the
optional final pool entry. -/
def replay? (v : Vipr) : Option (Option CheckerEntry) :=
  (replaySteps? v (initialPool v) (viprSteps v)).map Array.back?

def closedAbsurdB : Option CheckerEntry → Bool
  | none => false
  | some e => decide (e.2 = ∅) && absurdB e.1

def closedDominatesB (target : SLe) : Option CheckerEntry → Bool
  | none => false
  | some e => decide (e.2 = ∅) && domSLe e.1 target

def finalValidB (v : Vipr) (last? : Option CheckerEntry) : Bool :=
  match v.rtp with
  | .infeas => closedAbsurdB last?
  | .range lb ub =>
      if v.objSense = "min" then
        match lb with
        | none => true
        | some lower => closedDominatesB (objectiveLowerRow v lower) last?
      else if v.objSense = "max" then
        match ub with
        | none => true
        | some upper => closedDominatesB (objectiveUpperRow v upper) last?
      else false

/-- Production checker for both infeasibility and objective-range VIPR claims. -/
def checkVipr (v : Vipr) : Bool :=
  solSectionB v &&
  match replay? v with
  | none => false
  | some last? => finalValidB v last?

end LeanVIPR.Cert.ViprChecker
