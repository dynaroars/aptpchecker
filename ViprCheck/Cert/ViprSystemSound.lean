import ViprCheck.Cert.ViprSem

/-!
# Declarative soundness of the VIPR infeasibility proof system

This module separates the mathematical soundness of the VIPR proof rules from the
Boolean checker that recognizes them.

The certificate data remain exact rationals, but continuous valuations range over
`ℝ`, as in the semantics of mixed-integer linear programming.  Integer-declared
variables are required to be casts of integers.  `StepValid`, `DerivationValid`, and
`CertificateValid` are propositions: none of them invokes `linCheck`, `rndCheck`,
`svalidB`, `sfvalidB`, or `checkSemCore`.

The main theorem `proofSystem_sound` formalizes the hand proof from the VIPR
literature for infeasibility certificates using `asm`, `lin`, `rnd`, and `uns`.
It says that a declaratively valid derivation ending in a closed absurdity refutes
every real valuation satisfying the original rows and the declared integrality
conditions.
-/

namespace ViprCheck.Cert.ViprSystem

open ViprCheck.Cert

/-! ## Real semantics for rational VIPR rows -/

/-- A valuation of the MILP variables over the reals. -/
abbrev RealValuation := Nat → ℝ

/-- Evaluate a rational sparse linear form in a real valuation. -/
def evalReal (f : LinForm) (a : RealValuation) : ℝ :=
  (f.map (fun t => (t.coeff : ℝ) * a t.idx)).sum

/-- Satisfaction of a rational sensed row by a real valuation. -/
def satReal (c : SLe) (a : RealValuation) : Prop :=
  if c.sense = 'L' then evalReal c.form a ≤ (c.rhs : ℝ)
  else if c.sense = 'G' then (c.rhs : ℝ) ≤ evalReal c.form a
  else if c.sense = 'E' then evalReal c.form a = (c.rhs : ℝ)
  else False

/-- A real value is integral when it is the cast of an integer. -/
def IsIntReal (x : ℝ) : Prop := ∃ z : ℤ, x = (z : ℝ)

/-- Two rational forms denote the same real linear function. -/
def FormEqReal (f g : LinForm) : Prop := ∀ a, evalReal f a = evalReal g a

/-- A rational form denotes the zero real linear function. -/
def FormZeroReal (f : LinForm) : Prop := ∀ a, evalReal f a = 0

/-- A form is integer-valued whenever all declared integer variables are integral. -/
def FormIntegralReal (intVars : List Nat) (f : LinForm) : Prop :=
  ∀ a, (∀ j ∈ intVars, IsIntReal (a j)) → IsIntReal (evalReal f a)

@[simp] theorem evalReal_append (f g : LinForm) (a : RealValuation) :
    evalReal (f ++ g) a = evalReal f a + evalReal g a := by
  simp [evalReal]

@[simp] theorem evalReal_scale (q : ℚ) (f : LinForm) (a : RealValuation) :
    evalReal (LinForm.scale q f) a = (q : ℝ) * evalReal f a := by
  induction f with
  | nil => simp [LinForm.scale, evalReal]
  | cons t ts ih =>
      simp only [LinForm.scale, evalReal, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]
      push_cast
      ring

theorem evalReal_combineForm (comb : List (ℚ × Le)) (a : RealValuation) :
    evalReal (combineForm comb) a =
      (comb.map (fun p => (p.1 : ℝ) * evalReal p.2.form a)).sum := by
  induction comb with
  | nil => simp [combineForm, evalReal]
  | cons p ps ih =>
      simp only [combineForm, evalReal_append, evalReal_scale, ih, List.map_cons,
        List.sum_cons]

theorem evalReal_scomb (comb : List (ℚ × SLe)) (a : RealValuation) :
    evalReal (scomb comb).form a =
      (comb.map (fun p => (p.1 : ℝ) * evalReal p.2.form a)).sum := by
  simp only [scomb, combine, evalReal_combineForm, List.map_map]
  rfl

theorem scomb_rhs_real (comb : List (ℚ × SLe)) :
    ((scomb comb).rhs : ℝ) =
      (comb.map (fun p => (p.1 : ℝ) * (p.2.rhs : ℝ))).sum := by
  rw [scomb_rhs]
  change (Rat.castHom ℝ) (comb.map (fun p => p.1 * p.2.rhs)).sum = _
  rw [map_list_sum]
  apply congrArg List.sum
  rw [List.map_map]
  apply List.map_congr_left
  intro p _
  change ((p.1 * p.2.rhs : ℚ) : ℝ) = (p.1 : ℝ) * (p.2.rhs : ℝ)
  exact Rat.cast_mul p.1 p.2.rhs

/-! ## Suitable combinations and the `lin` rule -/

def senseSignReal (s : Char) : ℝ :=
  if s = 'L' then -1 else if s = 'G' then 1 else 0

def SuitableLe (cs : List (ℚ × SLe)) : Prop :=
  ∀ p ∈ cs, (p.1 : ℝ) * senseSignReal p.2.sense ≤ 0

def SuitableGe (cs : List (ℚ × SLe)) : Prop :=
  ∀ p ∈ cs, 0 ≤ (p.1 : ℝ) * senseSignReal p.2.sense

theorem term_le_real (lam : ℚ) (c : SLe) (a : RealValuation)
    (hsat : satReal c a) (hsuit : (lam : ℝ) * senseSignReal c.sense ≤ 0) :
    (lam : ℝ) * evalReal c.form a ≤ (lam : ℝ) * (c.rhs : ℝ) := by
  simp only [satReal, senseSignReal] at hsat hsuit
  split_ifs at hsat hsuit <;> (try rw [hsat]) <;> nlinarith [hsat, hsuit]

theorem term_ge_real (lam : ℚ) (c : SLe) (a : RealValuation)
    (hsat : satReal c a) (hsuit : 0 ≤ (lam : ℝ) * senseSignReal c.sense) :
    (lam : ℝ) * (c.rhs : ℝ) ≤ (lam : ℝ) * evalReal c.form a := by
  simp only [satReal, senseSignReal] at hsat hsuit
  split_ifs at hsat hsuit <;> (try rw [hsat]) <;> nlinarith [hsat, hsuit]

theorem comb_le_real (comb : List (ℚ × SLe)) (a : RealValuation)
    (hsuit : SuitableLe comb) (hsat : ∀ p ∈ comb, satReal p.2 a) :
    (comb.map (fun p => (p.1 : ℝ) * evalReal p.2.form a)).sum ≤
      (comb.map (fun p => (p.1 : ℝ) * (p.2.rhs : ℝ))).sum := by
  induction comb with
  | nil => simp
  | cons p ps ih =>
      simp only [List.map_cons, List.sum_cons]
      have hp := term_le_real p.1 p.2 a (hsat p (by simp)) (hsuit p (by simp))
      have ihp := ih (fun q hq => hsuit q (List.mem_cons.mpr (Or.inr hq)))
        (fun q hq => hsat q (List.mem_cons.mpr (Or.inr hq)))
      linarith

theorem comb_ge_real (comb : List (ℚ × SLe)) (a : RealValuation)
    (hsuit : SuitableGe comb) (hsat : ∀ p ∈ comb, satReal p.2 a) :
    (comb.map (fun p => (p.1 : ℝ) * (p.2.rhs : ℝ))).sum ≤
      (comb.map (fun p => (p.1 : ℝ) * evalReal p.2.form a)).sum := by
  induction comb with
  | nil => simp
  | cons p ps ih =>
      simp only [List.map_cons, List.sum_cons]
      have hp := term_ge_real p.1 p.2 a (hsat p (by simp)) (hsuit p (by simp))
      have ihp := ih (fun q hq => hsuit q (List.mem_cons.mpr (Or.inr hq)))
        (fun q hq => hsat q (List.mem_cons.mpr (Or.inr hq)))
      linarith

theorem scomb_le_real (comb : List (ℚ × SLe)) (a : RealValuation)
    (hsuit : SuitableLe comb) (hsat : ∀ p ∈ comb, satReal p.2 a) :
    evalReal (scomb comb).form a ≤ ((scomb comb).rhs : ℝ) := by
  rw [evalReal_scomb, scomb_rhs_real]
  exact comb_le_real comb a hsuit hsat

theorem scomb_ge_real (comb : List (ℚ × SLe)) (a : RealValuation)
    (hsuit : SuitableGe comb) (hsat : ∀ p ∈ comb, satReal p.2 a) :
    ((scomb comb).rhs : ℝ) ≤ evalReal (scomb comb).form a := by
  rw [evalReal_scomb, scomb_rhs_real]
  exact comb_ge_real comb a hsuit hsat

/-- A suitable combination that is already contradictory. -/
def LinAbsurd (cs : List (ℚ × SLe)) : Prop :=
  (SuitableLe cs ∧ FormZeroReal (scomb cs).form ∧ (scomb cs).rhs < 0) ∨
  (SuitableGe cs ∧ FormZeroReal (scomb cs).form ∧ 0 < (scomb cs).rhs)

/-- Declarative validity of a VIPR `lin` step. -/
def LinValid (stated : SLe) (cs : List (ℚ × SLe)) : Prop :=
  LinAbsurd cs ∨
  (FormEqReal (scomb cs).form stated.form ∧
    ((stated.sense = 'L' ∧ SuitableLe cs ∧ (scomb cs).rhs ≤ stated.rhs) ∨
     (stated.sense = 'G' ∧ SuitableGe cs ∧ stated.rhs ≤ (scomb cs).rhs)))

theorem linValid_sound {stated : SLe} {cs : List (ℚ × SLe)}
    (h : LinValid stated cs) {a : RealValuation}
    (hsat : ∀ p ∈ cs, satReal p.2 a) : satReal stated a := by
  rcases h with (⟨hsuit, hzero, hneg⟩ | ⟨hsuit, hzero, hpos⟩) |
      ⟨hform, ⟨hL, hsuit, hrhs⟩ | ⟨hG, hsuit, hrhs⟩⟩
  · have hle := scomb_le_real cs a hsuit hsat
    rw [hzero a] at hle
    have hnegR : ((scomb cs).rhs : ℝ) < 0 := by exact_mod_cast hneg
    exact (by linarith : False).elim
  · have hge := scomb_ge_real cs a hsuit hsat
    rw [hzero a] at hge
    have hposR : 0 < ((scomb cs).rhs : ℝ) := by exact_mod_cast hpos
    exact (by linarith : False).elim
  · have hle := scomb_le_real cs a hsuit hsat
    rw [hform a] at hle
    have hrhsR : ((scomb cs).rhs : ℝ) ≤ (stated.rhs : ℝ) := by exact_mod_cast hrhs
    simpa [satReal, hL] using le_trans hle hrhsR
  · have hge := scomb_ge_real cs a hsuit hsat
    rw [hform a] at hge
    have hrhsR : (stated.rhs : ℝ) ≤ ((scomb cs).rhs : ℝ) := by exact_mod_cast hrhs
    simpa [satReal, hG] using le_trans hrhsR hge

/-! ## The `rnd` rule -/

theorem rnd_le_real (form : LinForm) (β : ℚ) (a : RealValuation)
    (hInt : IsIntReal (evalReal form a)) (hsat : evalReal form a ≤ (β : ℝ)) :
    evalReal form a ≤ ((((⌊β⌋ : ℤ) : ℚ) : ℝ)) := by
  obtain ⟨m, hm⟩ := hInt
  rw [hm] at hsat ⊢
  have hmβ : (m : ℚ) ≤ β := by exact_mod_cast hsat
  have hfloor : m ≤ ⌊β⌋ := Int.le_floor.mpr hmβ
  exact_mod_cast hfloor

theorem rnd_ge_real (form : LinForm) (β : ℚ) (a : RealValuation)
    (hInt : IsIntReal (evalReal form a)) (hsat : (β : ℝ) ≤ evalReal form a) :
    ((((⌈β⌉ : ℤ) : ℚ) : ℝ)) ≤ evalReal form a := by
  obtain ⟨m, hm⟩ := hInt
  rw [hm] at hsat ⊢
  have hβm : β ≤ (m : ℚ) := by exact_mod_cast hsat
  have hceil : ⌈β⌉ ≤ m := Int.ceil_le.mpr hβm
  exact_mod_cast hceil

/-- Declarative validity of a VIPR `rnd` step. -/
def RndValid (intVars : List Nat) (stated : SLe) (cs : List (ℚ × SLe)) : Prop :=
  FormEqReal (scomb cs).form stated.form ∧
  FormIntegralReal intVars (scomb cs).form ∧
  ((stated.sense = 'L' ∧ SuitableLe cs ∧
      ((⌊(scomb cs).rhs⌋ : ℤ) : ℚ) ≤ stated.rhs) ∨
   (stated.sense = 'G' ∧ SuitableGe cs ∧
      stated.rhs ≤ ((⌈(scomb cs).rhs⌉ : ℤ) : ℚ)))

theorem rndValid_sound {intVars : List Nat} {stated : SLe} {cs : List (ℚ × SLe)}
    (h : RndValid intVars stated cs) {a : RealValuation}
    (hint : ∀ j ∈ intVars, IsIntReal (a j))
    (hsat : ∀ p ∈ cs, satReal p.2 a) : satReal stated a := by
  obtain ⟨hform, hInt, hdir⟩ := h
  rcases hdir with ⟨hL, hsuit, hrhs⟩ | ⟨hG, hsuit, hrhs⟩
  · have hle := scomb_le_real cs a hsuit hsat
    have hround := rnd_le_real (scomb cs).form (scomb cs).rhs a (hInt a hint) hle
    rw [hform a] at hround
    have hrhsR : (((((⌊(scomb cs).rhs⌋ : ℤ) : ℚ)) : ℝ)) ≤ (stated.rhs : ℝ) := by
      exact_mod_cast hrhs
    simpa [satReal, hL] using le_trans hround hrhsR
  · have hge := scomb_ge_real cs a hsuit hsat
    have hround := rnd_ge_real (scomb cs).form (scomb cs).rhs a (hInt a hint) hge
    rw [hform a] at hround
    have hrhsR : (stated.rhs : ℝ) ≤ (((((⌈(scomb cs).rhs⌉ : ℤ) : ℚ)) : ℝ)) := by
      exact_mod_cast hrhs
    simpa [satReal, hG] using le_trans hrhsR hround

/-! ## Domination, absurdities, and `uns` -/

/-- A sensed row is an absurdity over the reals. -/
def Absurd (c : SLe) : Prop :=
  FormZeroReal c.form ∧
  ((c.sense = 'L' ∧ c.rhs < 0) ∨
   (c.sense = 'G' ∧ 0 < c.rhs) ∨
   (c.sense = 'E' ∧ c.rhs ≠ 0))

theorem absurd_unsat {c : SLe} (h : Absurd c) (a : RealValuation) : ¬ satReal c a := by
  obtain ⟨hzero, hdir⟩ := h
  rcases hdir with ⟨hL, hneg⟩ | ⟨hG, hpos⟩ | ⟨hE, hne⟩
  · have hnegR : (c.rhs : ℝ) < 0 := by exact_mod_cast hneg
    simp [satReal, hL, hzero a, not_le.mpr hnegR]
  · have hposR : 0 < (c.rhs : ℝ) := by exact_mod_cast hpos
    simp [satReal, hG, hzero a, not_le.mpr hposR]
  · have hneR : (c.rhs : ℝ) ≠ 0 := by exact_mod_cast hne
    intro hs
    have heq : (0 : ℝ) = (c.rhs : ℝ) := by simpa [satReal, hE, hzero a] using hs
    exact hneR heq.symm

/-- Declarative VIPR domination. -/
def Dominates (c d : SLe) : Prop :=
  Absurd c ∨
  (FormEqReal c.form d.form ∧
    ((d.sense = 'L' ∧ (c.sense = 'L' ∨ c.sense = 'E') ∧ c.rhs ≤ d.rhs) ∨
     (d.sense = 'G' ∧ (c.sense = 'G' ∨ c.sense = 'E') ∧ d.rhs ≤ c.rhs) ∨
     (d.sense = 'E' ∧ c.sense = 'E' ∧ c.rhs = d.rhs)))

theorem dominates_sound {c d : SLe} (h : Dominates c d) {a : RealValuation}
    (hc : satReal c a) : satReal d a := by
  rcases h with habs | ⟨hform, hdir⟩
  · exact (absurd_unsat habs a hc).elim
  rcases hdir with ⟨hdL, hcL | hcE, hrhs⟩ |
      ⟨hdG, hcG | hcE, hrhs⟩ | ⟨hdE, hcE, hrhs⟩
  · have hc' : evalReal c.form a ≤ (c.rhs : ℝ) := by simpa [satReal, hcL] using hc
    have hrhsR : (c.rhs : ℝ) ≤ (d.rhs : ℝ) := by exact_mod_cast hrhs
    have hd' : evalReal d.form a ≤ (d.rhs : ℝ) := by
      rw [← hform a]
      exact le_trans hc' hrhsR
    simpa [satReal, hdL] using hd'
  · have hc' : evalReal c.form a = (c.rhs : ℝ) := by simpa [satReal, hcE] using hc
    have hrhsR : (c.rhs : ℝ) ≤ (d.rhs : ℝ) := by exact_mod_cast hrhs
    have hd' : evalReal d.form a ≤ (d.rhs : ℝ) := by
      rw [← hform a]
      exact hc'.le.trans hrhsR
    simpa [satReal, hdL] using hd'
  · have hc' : (c.rhs : ℝ) ≤ evalReal c.form a := by simpa [satReal, hcG] using hc
    have hrhsR : (d.rhs : ℝ) ≤ (c.rhs : ℝ) := by exact_mod_cast hrhs
    have hd' : (d.rhs : ℝ) ≤ evalReal d.form a := by
      rw [← hform a]
      exact hrhsR.trans hc'
    simpa [satReal, hdG] using hd'
  · have hc' : evalReal c.form a = (c.rhs : ℝ) := by simpa [satReal, hcE] using hc
    have hrhsR : (d.rhs : ℝ) ≤ (c.rhs : ℝ) := by exact_mod_cast hrhs
    have hd' : (d.rhs : ℝ) ≤ evalReal d.form a := by
      rw [← hform a]
      exact hrhsR.trans hc'.ge
    simpa [satReal, hdG] using hd'
  · have hc' : evalReal c.form a = (c.rhs : ℝ) := by simpa [satReal, hcE] using hc
    have hrhsR : (c.rhs : ℝ) = (d.rhs : ℝ) := by exact_mod_cast hrhs
    have hd' : evalReal d.form a = (d.rhs : ℝ) := by
      rw [← hform a]
      exact hc'.trans hrhsR
    simpa [satReal, hdE] using hd'

/-- Complementary integer bounds `f ≤ β` and `f ≥ β+1`, in either order. -/
def ComplementaryBounds (intVars : List Nat) (b1 b2 : SLe) : Prop :=
  (b1.sense = 'L' ∧ b2.sense = 'G' ∧ FormEqReal b1.form b2.form ∧
    FormIntegralReal intVars b1.form ∧ IsIntVal b1.rhs ∧ b2.rhs = b1.rhs + 1) ∨
  (b1.sense = 'G' ∧ b2.sense = 'L' ∧ FormEqReal b1.form b2.form ∧
    FormIntegralReal intVars b2.form ∧ IsIntVal b2.rhs ∧ b1.rhs = b2.rhs + 1)

theorem complementaryBounds_split {intVars : List Nat} {b1 b2 : SLe}
    (h : ComplementaryBounds intVars b1 b2) {a : RealValuation}
    (hint : ∀ j ∈ intVars, IsIntReal (a j)) : satReal b1 a ∨ satReal b2 a := by
  rcases h with ⟨h1, h2, hfe, hfi, hb, hb2⟩ | ⟨h1, h2, hfe, hfi, hb, hb2⟩
  · obtain ⟨m, hm⟩ := hfi a hint
    obtain ⟨n, hn⟩ := hb
    have hfe' := hfe a
    simp only [satReal, h1, h2]
    norm_num
    by_cases hmn : m ≤ n
    · left
      rw [hm, hn]
      exact_mod_cast hmn
    · right
      rw [hb2, hn, ← hfe', hm]
      have hnm : n + 1 ≤ m := by omega
      push_cast
      exact_mod_cast hnm
  · obtain ⟨m, hm⟩ := hfi a hint
    obtain ⟨n, hn⟩ := hb
    have hfe' := hfe a
    simp only [satReal, h1, h2]
    norm_num
    by_cases hmn : m ≤ n
    · right
      rw [hm, hn]
      exact_mod_cast hmn
    · left
      rw [hb2, hn, hfe', hm]
      have hnm : n + 1 ≤ m := by omega
      push_cast
      exact_mod_cast hnm

/-! ## Declarative derivations -/

/-- All references of a reason point to the current pool. -/
def ReferencesPast (pool : SPool) : SReason → Prop
  | .asm => True
  | .lin comb => ∀ p ∈ comb, p.2 < pool.length
  | .rnd comb => ∀ p ∈ comb, p.2 < pool.length
  | .uns i1 l1 i2 l2 =>
      i1 < pool.length ∧ l1 < pool.length ∧ i2 < pool.length ∧ l2 < pool.length
  | .sol => True

/-- Declarative validity of one VIPR derivation step. -/
def StepValid (intVars : List Nat) (pool : SPool) (s : SStep) : Prop :=
  ReferencesPast pool s.reason ∧
  match s.reason with
  | .asm => True
  | .lin comb => LinValid s.stated (resolve pool comb)
  | .rnd comb => RndValid intVars s.stated (resolve pool comb)
  | .uns i1 l1 i2 l2 =>
      Dominates (spoolRow pool i1) s.stated ∧
      Dominates (spoolRow pool i2) s.stated ∧
      ComplementaryBounds intVars (spoolRow pool l1) (spoolRow pool l2) ∧
      spoolRow pool l1 ∈ spoolAsm pool i1 ∧
      spoolRow pool l2 ∈ spoolAsm pool i2
  | .sol => False

/-- Declarative validity of a threaded derivation list. -/
def DerivationValid (intVars : List Nat) (pool : SPool) : List SStep → Prop
  | [] => True
  | s :: ss =>
      StepValid intVars pool s ∧
      DerivationValid intVars (pool ++ [sentryOf pool s]) ss

/-- A declaratively valid infeasibility certificate ends in a closed absurdity. -/
def CertificateValid (intVars : List Nat) (base : List SLe) (steps : List SStep) : Prop :=
  DerivationValid intVars (sinitPool base) steps ∧
  ∃ e, (sfreplay (sinitPool base) steps).getLast? = some e ∧ e.2 = ∅ ∧ Absurd e.1

/-- Semantic invariant for one replay-pool entry. -/
def EntryHolds (base : List SLe) (a : RealValuation) (e : SLe × SAsm) : Prop :=
  (∀ c ∈ base, satReal c a) → (∀ s ∈ e.2, satReal s a) → satReal e.1 a

theorem entryHolds_default (base : List SLe) (a : RealValuation) :
    EntryHolds base a sdflt := by
  intro _ _
  simp [sdflt, satReal, evalReal]

theorem entryHolds_getD (base : List SLe) (a : RealValuation) (pool : SPool)
    (hpool : ∀ e ∈ pool, EntryHolds base a e) (i : Nat) :
    EntryHolds base a (pool.getD i sdflt) := by
  by_cases h : i < pool.length
  · rw [List.getD_eq_getElem pool sdflt h]
    exact hpool _ (List.getElem_mem h)
  · rw [List.getD_eq_default pool sdflt (by omega)]
    exact entryHolds_default base a

theorem spoolRow_holds (base : List SLe) (a : RealValuation) (pool : SPool)
    (hpool : ∀ e ∈ pool, EntryHolds base a e) (i : Nat)
    (hbase : ∀ c ∈ base, satReal c a)
    (hasm : ∀ s ∈ spoolAsm pool i, satReal s a) :
    satReal (spoolRow pool i) a :=
  entryHolds_getD base a pool hpool i hbase hasm

/-- The Appendix-A induction: every declaratively valid replay entry is semantically
sound under its attached open assumptions. -/
theorem replay_holds (base : List SLe) (intVars : List Nat) (a : RealValuation)
    (hint : ∀ j ∈ intVars, IsIntReal (a j)) :
    ∀ (pool : SPool) (steps : List SStep),
      DerivationValid intVars pool steps →
      (∀ e ∈ pool, EntryHolds base a e) →
      ∀ e ∈ sfreplay pool steps, EntryHolds base a e := by
  intro pool steps
  induction steps generalizing pool with
  | nil =>
      intro _ hpool
      simpa [sfreplay] using hpool
  | cons s ss ih =>
      intro hv hpool
      obtain ⟨hstep, hrest⟩ := hv
      refine ih (pool ++ [sentryOf pool s]) hrest ?_
      intro e he
      rcases List.mem_append.mp he with he | he
      · exact hpool e he
      · rw [List.mem_singleton.mp he]
        obtain ⟨_, hrule⟩ := hstep
        cases hr : s.reason with
        | asm =>
            simp only [sentryOf, hr]
            intro _ hS
            exact hS s.stated (by simp)
        | lin comb =>
            simp only [hr] at hrule
            simp only [sentryOf, hr]
            intro hbase hS
            refine linValid_sound hrule (fun p hp => ?_)
            simp only [resolve, List.mem_map] at hp
            obtain ⟨q, hq, rfl⟩ := hp
            exact spoolRow_holds base a pool hpool q.2 hbase
              (fun t ht => hS t (mem_collectAsms hq ht))
        | rnd comb =>
            simp only [hr] at hrule
            simp only [sentryOf, hr]
            intro hbase hS
            refine rndValid_sound hrule hint (fun p hp => ?_)
            simp only [resolve, List.mem_map] at hp
            obtain ⟨q, hq, rfl⟩ := hp
            exact spoolRow_holds base a pool hpool q.2 hbase
              (fun t ht => hS t (mem_collectAsms hq ht))
        | uns i1 l1 i2 l2 =>
            simp only [hr] at hrule
            obtain ⟨hdom1, hdom2, hbnd, _, _⟩ := hrule
            simp only [sentryOf, hr]
            intro hbase hS
            rcases complementaryBounds_split hbnd hint with hb1 | hb2
            · refine dominates_sound hdom1 ?_
              refine spoolRow_holds base a pool hpool i1 hbase (fun t ht => ?_)
              by_cases hteq : t = spoolRow pool l1
              · rw [hteq]
                exact hb1
              · exact hS t (Finset.mem_union_left _
                  (Finset.mem_erase.mpr ⟨hteq, ht⟩))
            · refine dominates_sound hdom2 ?_
              refine spoolRow_holds base a pool hpool i2 hbase (fun t ht => ?_)
              by_cases hteq : t = spoolRow pool l2
              · rw [hteq]
                exact hb2
              · exact hS t (Finset.mem_union_right _
                  (Finset.mem_erase.mpr ⟨hteq, ht⟩))
        | sol =>
            simp [hr] at hrule

theorem initialPool_holds (base : List SLe) (a : RealValuation) :
    ∀ e ∈ sinitPool base, EntryHolds base a e := by
  intro e he
  simp only [sinitPool, List.mem_map] at he
  obtain ⟨c, hc, rfl⟩ := he
  intro hbase _
  exact hbase c hc

/-- **VIPR proof-system soundness over real continuous valuations.**

This theorem is independent of the executable checker.  It formalizes:

`declaratively valid closed VIPR refutation → real/integer MILP infeasible`.
-/
theorem proofSystem_sound (base : List SLe) (intVars : List Nat) (steps : List SStep)
    (hvalid : CertificateValid intVars base steps) :
    ∀ a : RealValuation,
      (∀ j ∈ intVars, IsIntReal (a j)) →
      (∀ c ∈ base, satReal c a) →
      False := by
  intro a hint hbase
  obtain ⟨hder, e, hlast, hclosed, habs⟩ := hvalid
  have hall := replay_holds base intVars a hint (sinitPool base) steps hder
    (initialPool_holds base a)
  have he : EntryHolds base a e := hall e (List.mem_of_getLast? hlast)
  have hsat : satReal e.1 a := he hbase (by simp [hclosed])
  exact absurd_unsat habs a hsat

end ViprCheck.Cert.ViprSystem
