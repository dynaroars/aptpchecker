import AptpCheck.Cert.Vipr

/-!
# Verified flat-derivation checker (no reshaper)

A checker that consumes SCIP's VIPR proof as a **flat, index-referenced derivation
list** directly, so there is no untrusted flat→tree conversion on the checking path.
Each derived row carries the set of assumption rows it still depends on; `asm`
introduces one, `lin` unions them, and `uns` (an integer case-split) discharges the two
branch bounds. The final derived row must be an absurdity (`0 ≤ negative`) with an
empty assumption set. Soundness reuses the proven step lemmas `lin_sound`,
`int_split`, `sat_leLower`/`sat_leUpper` from `Cert/Vipr`.

This module proves the mathematical core (reasons `asm`, `lin`, `uns`); `rnd`, a `Bool`
front-end, and the adapter from the parsed `Ast.Vipr` build on it.
-/

namespace AptpCheck.Cert

/-- Pool of derived facts: each a row paired with the assumption rows it depends on. -/
abbrev Pool := List (Le × List Le)

/-- Default pool entry: the trivially-true row `0 ≤ 0` with no assumptions. -/
def dflt : Le × List Le := (⟨[], 0⟩, [])

def poolRow (pool : Pool) (i : Nat) : Le := (pool.getD i dflt).1
def poolAsm (pool : Pool) (i : Nat) : List Le := (pool.getD i dflt).2

/-- A flat derivation step. `asm r` introduces bound `r`; `lin comb` is a nonnegative
combination of earlier pool rows (by index); `uns i1 i2 j k` merges the two branches
of the integer split `x_j ≤ k`/`x_j ≥ k+1` on children `i1`,`i2`. -/
inductive FReason where
  | asm (r : Le)
  | lin (comb : List (ℚ × Nat))
  | rnd (comb : List (ℚ × Nat))
  | uns (i1 i2 j : Nat) (k : ℤ)

/-- The pool entry a step produces. -/
def entryOf (pool : Pool) : FReason → (Le × List Le)
  | .asm r => (r, [r])
  | .lin comb =>
      (combine (comb.map (fun p => (p.1, poolRow pool p.2))),
       comb.flatMap (fun p => poolAsm pool p.2))
  | .rnd comb =>
      (deriveRow (comb.map (fun p => (p.1, poolRow pool p.2))) true,
       comb.flatMap (fun p => poolAsm pool p.2))
  | .uns i1 i2 j k =>
      (poolRow pool i1,
       (poolAsm pool i1).erase (leLower j (k : ℚ)) ++ (poolAsm pool i2).erase (leUpper j (k : ℚ)))

/-- Well-formedness of a step against the current pool and the integer-var set. `rnd`
additionally requires the combined form to be integer-valued (integer coefficients on
integer-declared variables), which justifies rounding the constant down. -/
def rvalid (intVars : List Nat) (pool : Pool) : FReason → Prop
  | .asm _ => True
  | .lin comb => ∀ p ∈ comb, 0 ≤ p.1
  | .rnd comb =>
      (∀ p ∈ comb, 0 ≤ p.1) ∧
      (∀ t ∈ combineForm (comb.map (fun p => (p.1, poolRow pool p.2))),
        IsIntVal t.coeff ∧ t.idx ∈ intVars)
  | .uns i1 i2 j k =>
      j ∈ intVars ∧ poolRow pool i1 = poolRow pool i2 ∧
      leLower j (k : ℚ) ∈ poolAsm pool i1 ∧ leUpper j (k : ℚ) ∈ poolAsm pool i2

/-- `e` holds at `a`: if `a` satisfies the base (CON) rows and all of `e`'s assumption
rows, then `e`'s row holds. -/
def entryHolds (base : List Le) (a : Valuation) (e : Le × List Le) : Prop :=
  (∀ c ∈ base, Le.sat c a) → (∀ s ∈ e.2, Le.sat s a) → Le.sat e.1 a

/-- Replay the steps, growing the pool. -/
def freplay (pool : Pool) : List FReason → Pool
  | [] => pool
  | r :: rs => freplay (pool ++ [entryOf pool r]) rs

/-- The replay is valid if every step is well-formed against the pool it sees. -/
def fvalid (intVars : List Nat) (pool : Pool) : List FReason → Prop
  | [] => True
  | r :: rs => rvalid intVars pool r ∧ fvalid intVars (pool ++ [entryOf pool r]) rs

/-- The default entry always holds. -/
theorem entryHolds_dflt (base : List Le) (a : Valuation) : entryHolds base a dflt := by
  intro _ _; show Le.sat (⟨[], 0⟩ : Le) a
  simp [Le.sat, LinForm.eval]

/-- Every indexed lookup into a pool of holding entries holds. -/
theorem entryHolds_getD (base : List Le) (a : Valuation) (pool : Pool)
    (hpool : ∀ e ∈ pool, entryHolds base a e) (i : Nat) :
    entryHolds base a (pool.getD i dflt) := by
  by_cases h : i < pool.length
  · rw [List.getD_eq_getElem pool dflt h]; exact hpool _ (List.getElem_mem h)
  · rw [List.getD_eq_default pool dflt (by omega)]; exact entryHolds_dflt base a

/-- The row and assumptions of a holding indexed entry (convenience). -/
theorem poolRow_holds (base : List Le) (a : Valuation) (pool : Pool)
    (hpool : ∀ e ∈ pool, entryHolds base a e) (i : Nat)
    (hbase : ∀ c ∈ base, Le.sat c a) (hasm : ∀ s ∈ poolAsm pool i, Le.sat s a) :
    Le.sat (poolRow pool i) a :=
  entryHolds_getD base a pool hpool i hbase hasm

/-- Soundness of one `rnd` step over an abstract combination: a nonnegative combination
of satisfied `≤`-rows whose combined form is integer-valued yields the rounded-down
constraint. Stated over an abstract `comb'` to keep elaboration cheap. -/
theorem rnd_sat (comb' : List (ℚ × Le)) (a : Valuation)
    (hnn : ∀ q ∈ comb', 0 ≤ q.1) (hsat : ∀ q ∈ comb', Le.sat q.2 a)
    (hInt : ∀ t ∈ combineForm comb', IsIntVal t.coeff ∧ IsIntVal (a t.idx)) :
    Le.sat (deriveRow comb' true) a := by
  have hr := rnd_sound (combineForm comb') (combine comb').rhs a
    (LinForm.eval_isInt (combineForm comb') a hInt) (lin_sound comb' a hnn hsat)
  simpa [deriveRow] using hr

/-- Definitional shape of a `rnd` entry (used to expose the combination for
`generalize`, keeping the floor/coercion defeq over a plain variable). -/
theorem entryOf_rnd (pool : Pool) (comb : List (ℚ × Nat)) :
    entryOf pool (FReason.rnd comb) =
      (deriveRow (comb.map (fun p => (p.1, poolRow pool p.2))) true,
       comb.flatMap (fun p => poolAsm pool p.2)) := rfl

/-- **Core soundness of the flat replay.** If the replay is valid and every current
pool entry holds at `a`, then every entry of the replayed pool holds at `a`. -/
theorem freplay_holds (base : List Le) (intVars : List Nat) (a : Valuation)
    (hint : ∀ j ∈ intVars, IsIntVal (a j)) :
    ∀ (pool : Pool) (steps : List FReason),
      fvalid intVars pool steps → (∀ e ∈ pool, entryHolds base a e) →
      ∀ e ∈ freplay pool steps, entryHolds base a e := by
  intro pool steps
  induction steps generalizing pool with
  | nil => intro _ hpool; simpa [freplay] using hpool
  | cons r rs ih =>
      intro hv hpool
      obtain ⟨hr, hrest⟩ := hv
      refine ih (pool ++ [entryOf pool r]) hrest ?_
      intro e he
      rcases List.mem_append.mp he with h | h
      · exact hpool e h
      · rw [List.mem_singleton.mp h]
        -- prove entryHolds base a (entryOf pool r), by cases on the reason
        cases r with
        | asm rr =>
            intro _ hs; exact hs rr (by simp [entryOf])
        | lin comb =>
            intro hbase hS
            show Le.sat (combine (comb.map (fun p => (p.1, poolRow pool p.2)))) a
            refine lin_sound _ a ?_ ?_
            · intro q hq
              simp only [List.mem_map] at hq
              obtain ⟨p, hp, rfl⟩ := hq
              exact hr p hp
            · intro q hq
              simp only [List.mem_map] at hq
              obtain ⟨p, hp, rfl⟩ := hq
              refine poolRow_holds base a pool hpool p.2 hbase (fun s hs => ?_)
              exact hS s (List.mem_flatMap.mpr ⟨p, hp, hs⟩)
        | rnd comb =>
            obtain ⟨hnn, hintg⟩ := hr
            rw [entryOf_rnd]
            intro hbase hS
            have h1 : ∀ q ∈ comb.map (fun p => (p.1, poolRow pool p.2)), 0 ≤ q.1 := by
              intro q hq; simp only [List.mem_map] at hq
              obtain ⟨p, hp, rfl⟩ := hq; exact hnn p hp
            have h2 : ∀ q ∈ comb.map (fun p => (p.1, poolRow pool p.2)), Le.sat q.2 a := by
              intro q hq; simp only [List.mem_map] at hq
              obtain ⟨p, hp, rfl⟩ := hq
              exact poolRow_holds base a pool hpool p.2 hbase
                (fun s hs => hS s (List.mem_flatMap.mpr ⟨p, hp, hs⟩))
            have h3 : ∀ t ∈ combineForm (comb.map (fun p => (p.1, poolRow pool p.2))),
                IsIntVal t.coeff ∧ IsIntVal (a t.idx) :=
              fun t ht => ⟨(hintg t ht).1, hint t.idx (hintg t ht).2⟩
            generalize comb.map (fun p => (p.1, poolRow pool p.2)) = cc at h1 h2 h3 ⊢
            exact rnd_sat cc a h1 h2 h3
        | uns i1 i2 j k =>
            obtain ⟨hj, hEq, hlo, hup⟩ := hr
            intro hbase hS
            show Le.sat (poolRow pool i1) a
            obtain ⟨v, hv⟩ := hint j hj
            -- assumptions of a branch child hold once its branch bound holds
            have branch : ∀ (i : Nat) (bnd : Le),
                bnd ∈ poolAsm pool i → Le.sat bnd a →
                ((poolAsm pool i).erase bnd) ⊆ (poolAsm pool i1).erase (leLower j (k:ℚ))
                  ++ (poolAsm pool i2).erase (leUpper j (k:ℚ)) →
                Le.sat (poolRow pool i) a := by
              intro i bnd _ hbnd hsub
              refine poolRow_holds base a pool hpool i hbase (fun s hs => ?_)
              by_cases hsb : s = bnd
              · rw [hsb]; exact hbnd
              · exact hS s (hsub ((List.mem_erase_of_ne hsb).mpr hs))
            rcases int_split a j k v hv with hle | hge
            · exact branch i1 (leLower j (k:ℚ)) hlo ((sat_leLower a j (k:ℚ)).mpr hle)
                (fun s hs => List.mem_append_left _ hs)
            · rw [hEq]
              exact branch i2 (leUpper j (k:ℚ)) hup ((sat_leUpper a j (k:ℚ)).mpr hge)
                (fun s hs => List.mem_append_right _ hs)

/-- The initial pool: each base (CON) row with no assumptions. -/
def initPool (base : List Le) : Pool := base.map (fun c => (c, ([] : List Le)))

theorem initPool_holds (base : List Le) (a : Valuation) :
    ∀ e ∈ initPool base, entryHolds base a e := by
  intro e he
  simp only [initPool, List.mem_map] at he
  obtain ⟨c, hc, rfl⟩ := he
  intro hbase _; exact hbase c hc

/-- **Flat certificate ⟹ infeasibility.** If a valid flat replay from the base rows
produces an absurdity (an identically-zero form with negative constant) carrying no
open assumptions, then no valuation whose integer-declared variables are integral
satisfies the base rows. -/
theorem flat_infeasible (base : List Le) (intVars : List Nat) (steps : List FReason)
    (hv : fvalid intVars (initPool base) steps)
    (e : Le × List Le) (hemem : e ∈ freplay (initPool base) steps)
    (hasm : e.2 = []) (hzero : ∀ a, e.1.form.eval a = 0) (hneg : e.1.rhs < 0) :
    ∀ a, (∀ j ∈ intVars, IsIntVal (a j)) → (∀ c ∈ base, Le.sat c a) → False := by
  intro a hint hbase
  have hall := freplay_holds base intVars a hint (initPool base) steps hv (initPool_holds base a)
  have hE : entryHolds base a e := hall e hemem
  have hsat : Le.sat e.1 a := hE hbase (by rw [hasm]; intro s hs; simp at hs)
  rw [Le.sat, hzero a] at hsat
  linarith

/-! ## Runnable `Bool` checker -/

/-- Decidable well-formedness of a step. -/
def rvalidB (intVars : List Nat) (pool : Pool) : FReason → Bool
  | .asm _ => true
  | .lin comb => comb.all (fun p => decide (0 ≤ p.1))
  | .rnd comb =>
      comb.all (fun p => decide (0 ≤ p.1)) &&
      (combineForm (comb.map (fun p => (p.1, poolRow pool p.2)))).all
        (fun t => isIntValB t.coeff && decide (t.idx ∈ intVars))
  | .uns i1 i2 j k =>
      decide (j ∈ intVars) && (poolRow pool i1 == poolRow pool i2) &&
      decide (leLower j (k : ℚ) ∈ poolAsm pool i1) && decide (leUpper j (k : ℚ) ∈ poolAsm pool i2)

theorem rvalidB_valid (intVars : List Nat) (pool : Pool) (r : FReason)
    (h : rvalidB intVars pool r = true) : rvalid intVars pool r := by
  cases r with
  | asm r => trivial
  | lin comb =>
      intro p hp; exact of_decide_eq_true ((List.all_eq_true.mp h) p hp)
  | rnd comb =>
      simp only [rvalidB, Bool.and_eq_true] at h
      refine ⟨fun p hp => of_decide_eq_true ((List.all_eq_true.mp h.1) p hp), fun t ht => ?_⟩
      have ht2 := (List.all_eq_true.mp h.2) t ht
      rw [Bool.and_eq_true] at ht2
      exact ⟨isIntValB_sound ht2.1, of_decide_eq_true ht2.2⟩
  | uns i1 i2 j k =>
      simp only [rvalidB, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨h.1.1.1, eq_of_beq h.1.1.2, h.1.2, h.2⟩

def fvalidB (intVars : List Nat) (pool : Pool) : List FReason → Bool
  | [] => true
  | r :: rs => rvalidB intVars pool r && fvalidB intVars (pool ++ [entryOf pool r]) rs

theorem fvalidB_valid (intVars : List Nat) :
    ∀ (pool : Pool) (steps : List FReason),
      fvalidB intVars pool steps = true → fvalid intVars pool steps := by
  intro pool steps
  induction steps generalizing pool with
  | nil => intro _; trivial
  | cons r rs ih =>
      intro h
      simp only [fvalidB, Bool.and_eq_true] at h
      exact ⟨rvalidB_valid intVars pool r h.1, ih _ h.2⟩

/-- Acceptance: the last derived row is a zero-form negative-constant absurdity with no
open assumptions. -/
def acceptB (pool : Pool) : Bool :=
  match pool.getLast? with
  | some e => e.2.isEmpty && formIsZero e.1.form && decide (e.1.rhs < 0)
  | none => false

/-- The runnable checker: a valid replay from the base rows ending in an accepted
absurdity. -/
def checkFlat (intVars : List Nat) (base : List Le) (steps : List FReason) : Bool :=
  fvalidB intVars (initPool base) steps && acceptB (freplay (initPool base) steps)

/-- **The runnable flat checker is sound.** If `checkFlat` accepts, no valuation with
the integer-declared variables integral satisfies the base rows. -/
theorem checkFlat_sound (intVars : List Nat) (base : List Le) (steps : List FReason)
    (h : checkFlat intVars base steps = true) :
    ∀ a, (∀ j ∈ intVars, IsIntVal (a j)) → (∀ c ∈ base, Le.sat c a) → False := by
  simp only [checkFlat, Bool.and_eq_true] at h
  obtain ⟨hval, hacc⟩ := h
  have hv := fvalidB_valid intVars _ steps hval
  rcases hgl : (freplay (initPool base) steps).getLast? with _ | e
  · exact absurd hacc (by simp [acceptB, hgl])
  · simp only [acceptB, hgl, Bool.and_eq_true, decide_eq_true_eq] at hacc
    obtain ⟨⟨hemp, hfz⟩, hneg⟩ := hacc
    have hasm : e.2 = [] := by cases hc : e.2 with | nil => rfl | cons a t => rw [hc] at hemp; simp at hemp
    exact flat_infeasible base intVars steps hv e (List.mem_of_getLast? hgl) hasm
      (fun a => formIsZero_sound e.1.form hfz a) hneg

end AptpCheck.Cert
