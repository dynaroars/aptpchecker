import AptpCheck.Cert.LinCon

/-!
# Soundness of VIPR derivation replay (`lin`, `rnd`, `uns`) and a checked fold

A VIPR certificate is a list of *derived* constraints `DER`, each justified by a
*reason*.  This module proves the soundness of the three derivation rules the
checker actually reasons about, working over the sparse `Le` / `LinForm` /
`Valuation` representation of `AptpCheck.Cert.LinCon`:

* **`lin`** — a nonnegative rational combination of earlier `≤`-rows.  We build the
  combined row `combine comb` explicitly and prove `lin_sound`: if every used row
  holds at `a` (with nonnegative multipliers) then the combined row holds at `a`.
  This generalizes `farkas_le` from "combination cancels to a negative constant ⟹
  infeasible" to "the derived row is *implied*"; `lin_absurd` recovers the
  absurdity form.

* **`rnd`** — integer rounding.  `rnd_sound`: if `form ≤ β` holds at `a` and
  `form.eval a` is an integer (because every involved variable and coefficient is
  integral, cf. `LinForm.eval_isInt`) then `form ≤ ⌊β⌋` holds at `a`.

* **`uns`** — an integer split `x_i ≤ k ∨ x_i ≥ k+1` on an integer-valued
  variable.  `uns_sound`: if the derived row holds on each branch, it holds
  unconditionally at `a`.

Finally `replay_sat` / `replay_infeasible*` give a genuinely *checked fold* for the
assumption-free, `lin`-only certificate shape: replaying the steps grows a pool of
rows all implied by the original `CON` rows, and a final Farkas combination over that
pool refutes the system (reusing `farkas_le`).  Assumption sets (`asm`), the `rnd`
and `uns` rules inside the automatic fold, and `sol` are *not* threaded by the fold
yet; they are available as standalone lemmas above.
-/

namespace AptpCheck.Cert

open Classical

variable {α : Type*}

/-- Pointwise-`≤` implies `≤` on list sums (local re-derivation; the `LinCon` copy is
`private`). -/
theorem list_sum_le (l : List α) (f g : α → ℚ)
    (h : ∀ x ∈ l, f x ≤ g x) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.sum_cons]
      have h0 : f a ≤ g a := h a (by simp)
      have iht : (t.map f).sum ≤ (t.map g).sum :=
        ih (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))
      linarith

/-! ## Combining rows (`lin`) -/

/-- Scale every coefficient of a linear form by `y`. -/
def LinForm.scale (y : ℚ) (f : LinForm) : LinForm :=
  f.map (fun t => ⟨t.idx, y * t.coeff⟩)

@[simp] theorem LinForm.eval_append (f g : LinForm) (a : Valuation) :
    (f ++ g).eval a = f.eval a + g.eval a := by
  unfold LinForm.eval
  rw [List.map_append, List.sum_append]

@[simp] theorem LinForm.eval_scale (y : ℚ) (f : LinForm) (a : Valuation) :
    (LinForm.scale y f).eval a = y * f.eval a := by
  induction f with
  | nil => simp [LinForm.scale, LinForm.eval]
  | cons t ts ih =>
      unfold LinForm.scale LinForm.eval
      simp only [List.map_cons, List.sum_cons]
      -- reduce the tail via the induction hypothesis (stated with `scale`/`eval`)
      have key : ((ts.map (fun t => (⟨t.idx, y * t.coeff⟩ : Term))).map
                    (fun t => t.coeff * a t.idx)).sum
                = y * (ts.map (fun t => t.coeff * a t.idx)).sum := by
        have := ih
        unfold LinForm.scale LinForm.eval at this
        simpa using this
      rw [key]; ring

/-- The linear form of a nonnegative combination `[(y₁,c₁), …]`: the concatenation of
the scaled forms `yᵢ · cᵢ.form`. -/
def combineForm : List (ℚ × Le) → LinForm
  | [] => []
  | p :: ps => LinForm.scale p.1 p.2.form ++ combineForm ps

theorem eval_combineForm (comb : List (ℚ × Le)) (a : Valuation) :
    (combineForm comb).eval a = (comb.map (fun p => p.1 * p.2.form.eval a)).sum := by
  induction comb with
  | nil => simp [combineForm, LinForm.eval]
  | cons p ps ih =>
      simp only [combineForm, LinForm.eval_append, LinForm.eval_scale, ih,
        List.map_cons, List.sum_cons]

/-- The `Le` obtained from a nonnegative combination of rows: linear part
`combineForm comb`, right-hand side `Σ yᵢ · cᵢ.rhs`. -/
def combine (comb : List (ℚ × Le)) : Le :=
  ⟨combineForm comb, (comb.map (fun p => p.1 * p.2.rhs)).sum⟩

/-- **`lin` soundness (general form).**  If every row used in a nonnegative
combination holds at `a`, so does the combined row.  This is the "implication"
generalization of `farkas_le`. -/
theorem lin_sound (comb : List (ℚ × Le)) (a : Valuation)
    (hnn : ∀ p ∈ comb, 0 ≤ p.1)
    (hsat : ∀ p ∈ comb, Le.sat p.2 a) :
    Le.sat (combine comb) a := by
  show (combine comb).form.eval a ≤ (combine comb).rhs
  simp only [combine, eval_combineForm]
  apply list_sum_le comb (fun p => p.1 * p.2.form.eval a) (fun p => p.1 * p.2.rhs)
  intro p hp
  exact mul_le_mul_of_nonneg_left (hsat p hp) (hnn p hp)

/-- **`lin` to absurdity.**  If the combined row cancels to `0` at `a` and its
constant is negative, the used rows cannot all hold at `a`.  (Recovers the content of
`farkas_le` from the general `lin_sound`.) -/
theorem lin_absurd (comb : List (ℚ × Le)) (a : Valuation)
    (hnn : ∀ p ∈ comb, 0 ≤ p.1)
    (hsat : ∀ p ∈ comb, Le.sat p.2 a)
    (hz : (combine comb).form.eval a = 0)
    (hneg : (combine comb).rhs < 0) : False := by
  have h := lin_sound comb a hnn hsat
  rw [Le.sat, hz] at h
  linarith

/-! ## Integer rounding (`rnd`) -/

/-- A rational is integral if it is the cast of some integer. -/
def IsIntVal (q : ℚ) : Prop := ∃ n : ℤ, q = (n : ℚ)

theorem isIntVal_cast (n : ℤ) : IsIntVal ((n : ℚ)) := ⟨n, rfl⟩

/-- If every term of a form has integral coefficient and integral variable value at
`a`, the form evaluates to an integer at `a`. -/
theorem LinForm.eval_isInt (f : LinForm) (a : Valuation)
    (h : ∀ t ∈ f, IsIntVal t.coeff ∧ IsIntVal (a t.idx)) :
    IsIntVal (f.eval a) := by
  induction f with
  | nil => exact ⟨0, by simp [LinForm.eval]⟩
  | cons t ts ih =>
      obtain ⟨⟨c, hc⟩, ⟨v, hv⟩⟩ := h t (by simp)
      obtain ⟨m, hm⟩ := ih (fun t' ht' => h t' (List.mem_cons_of_mem _ ht'))
      refine ⟨c * v + m, ?_⟩
      have hm' : (ts.map (fun t => t.coeff * a t.idx)).sum = (m : ℚ) := hm
      simp only [LinForm.eval, List.map_cons, List.sum_cons]
      rw [hc, hv, hm']
      push_cast; ring

/-- **`rnd` soundness.**  If `form ≤ β` at `a` and `form.eval a` is an integer, then
`form ≤ ⌊β⌋` at `a`. -/
theorem rnd_sound (form : LinForm) (β : ℚ) (a : Valuation)
    (hInt : IsIntVal (form.eval a))
    (hsat : Le.sat ⟨form, β⟩ a) :
    Le.sat ⟨form, ((⌊β⌋ : ℤ) : ℚ)⟩ a := by
  obtain ⟨n, hn⟩ := hInt
  show form.eval a ≤ ((⌊β⌋ : ℤ) : ℚ)
  have hsat' : form.eval a ≤ β := hsat
  have hnβ : (n : ℚ) ≤ β := by rw [← hn]; exact hsat'
  have hfloor : n ≤ ⌊β⌋ := Int.le_floor.mpr hnβ
  rw [hn]; exact_mod_cast hfloor

/-- Convenience form of `rnd` soundness discharging integrality from the terms. -/
theorem rnd_sound_of_terms (form : LinForm) (β : ℚ) (a : Valuation)
    (hterms : ∀ t ∈ form, IsIntVal t.coeff ∧ IsIntVal (a t.idx))
    (hsat : Le.sat ⟨form, β⟩ a) :
    Le.sat ⟨form, ((⌊β⌋ : ℤ) : ℚ)⟩ a :=
  rnd_sound form β a (LinForm.eval_isInt form a hterms) hsat

/-! ## Integer split (`uns`) -/

/-- The branch constraint `x_i ≤ k`. -/
def leLower (i : Nat) (k : ℚ) : Le := ⟨[⟨i, 1⟩], k⟩
/-- The branch constraint `x_i ≥ k+1`, normalized to `-x_i ≤ -(k+1)`. -/
def leUpper (i : Nat) (k : ℚ) : Le := ⟨[⟨i, -1⟩], -(k + 1)⟩

theorem sat_leLower (a : Valuation) (i : Nat) (k : ℚ) :
    Le.sat (leLower i k) a ↔ a i ≤ k := by
  unfold leLower Le.sat LinForm.eval
  simp

theorem sat_leUpper (a : Valuation) (i : Nat) (k : ℚ) :
    Le.sat (leUpper i k) a ↔ k + 1 ≤ a i := by
  unfold leUpper Le.sat LinForm.eval
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  constructor <;> intro h <;> linarith

/-- The integer split is exhaustive when `a i` is integer-valued. -/
theorem int_split (a : Valuation) (i : Nat) (k v : ℤ) (hv : a i = (v : ℚ)) :
    a i ≤ (k : ℚ) ∨ (k : ℚ) + 1 ≤ a i := by
  by_cases h : v ≤ k
  · exact Or.inl (by rw [hv]; exact_mod_cast h)
  · refine Or.inr ?_
    rw [hv]
    have hlt : k < v := lt_of_not_ge h
    have hkv : (k : ℤ) + 1 ≤ v := Int.add_one_le_iff.mpr hlt
    exact_mod_cast hkv

/-- **`uns` soundness (integer split discharge).**  For an integer-valued variable
`x_i = a i`, if a row `d` holds whenever the lower branch `x_i ≤ k` holds and also
whenever the upper branch `x_i ≥ k+1` holds, then `d` holds unconditionally at `a`. -/
theorem uns_sound (a : Valuation) (d : Le) (i : Nat) (k v : ℤ)
    (hv : a i = (v : ℚ))
    (hle : Le.sat (leLower i (k : ℚ)) a → Le.sat d a)
    (hge : Le.sat (leUpper i (k : ℚ)) a → Le.sat d a) :
    Le.sat d a := by
  rcases int_split a i k v hv with h | h
  · exact hle ((sat_leLower a i (k : ℚ)).mpr h)
  · exact hge ((sat_leUpper a i (k : ℚ)).mpr h)

/-! ## Checked fold: assumption-free, `lin`-only replay -/

/-- Extend a pool of rows by one `lin` step (append the combined row). -/
def stepPool (pool : List Le) (comb : List (ℚ × Le)) : List Le :=
  pool ++ [combine comb]

/-- Pool of rows after replaying a list of `lin` steps, threaded left to right. -/
def replay (pool : List Le) : List (List (ℚ × Le)) → List Le
  | [] => pool
  | comb :: rest => replay (stepPool pool comb) rest

/-- A replay is *valid* if every step uses only rows already in the pool, with
nonnegative multipliers.  Threaded exactly like `replay`. -/
def replayValid (pool : List Le) : List (List (ℚ × Le)) → Prop
  | [] => True
  | comb :: rest =>
      (∀ p ∈ comb, 0 ≤ p.1) ∧ (∀ p ∈ comb, p.2 ∈ pool) ∧
      replayValid (stepPool pool comb) rest

/-- **Replay invariant.**  If the replay is valid and every pool row holds at `a`,
then every row of the final pool holds at `a`. -/
theorem replay_sat (a : Valuation) :
    ∀ (pool : List Le) (steps : List (List (ℚ × Le))),
      replayValid pool steps → (∀ c ∈ pool, Le.sat c a) →
      ∀ c ∈ replay pool steps, Le.sat c a := by
  intro pool steps
  induction steps generalizing pool with
  | nil => intro _ hpool; simpa [replay] using hpool
  | cons comb rest ih =>
      intro hv hpool
      obtain ⟨hnn, hused, hrest⟩ := hv
      refine ih (stepPool pool comb) hrest ?_
      intro c hc
      rcases List.mem_append.mp hc with h | h
      · exact hpool c h
      · rw [List.mem_singleton.mp h]
        exact lin_sound comb a hnn (fun p hp => hpool p.2 (hused p hp))

/-- **Checked replay ⟹ infeasibility (at a fixed valuation).**  If the replay is
valid, a final Farkas combination over the resulting pool cancels at `a` and is
negative, and `a` satisfies the original rows, then `False`. -/
theorem replay_infeasible (rows : List Le) (steps : List (List (ℚ × Le)))
    (hvalid : replayValid rows steps)
    (final : List (ℚ × Le))
    (hnn : ∀ p ∈ final, 0 ≤ p.1)
    (hused : ∀ p ∈ final, p.2 ∈ replay rows steps)
    (a : Valuation)
    (hcancel : (final.map (fun p => p.1 * p.2.form.eval a)).sum = 0)
    (hneg : (final.map (fun p => p.1 * p.2.rhs)).sum < 0)
    (hrows : ∀ c ∈ rows, Le.sat c a) : False := by
  have hpool := replay_sat a rows steps hvalid hrows
  exact farkas_le final a hnn hcancel hneg (fun p hp => hpool p.2 (hused p hp))

/-- **Checked replay ⟹ infeasibility (over all valuations).**  If the final Farkas
combination cancels *identically* (at every valuation) and is negative, then no
valuation satisfies the original rows — the certificate proves the system infeasible. -/
theorem replay_infeasible_all (rows : List Le) (steps : List (List (ℚ × Le)))
    (hvalid : replayValid rows steps)
    (final : List (ℚ × Le))
    (hnn : ∀ p ∈ final, 0 ≤ p.1)
    (hused : ∀ p ∈ final, p.2 ∈ replay rows steps)
    (hcancel : ∀ a, (final.map (fun p => p.1 * p.2.form.eval a)).sum = 0)
    (hneg : (final.map (fun p => p.1 * p.2.rhs)).sum < 0) :
    ∀ a, (∀ c ∈ rows, Le.sat c a) → False :=
  fun a hrows =>
    replay_infeasible rows steps hvalid final hnn hused a (hcancel a) hneg hrows

/-! ## Branch-and-bound refutation trees: the automatic "proof by cases" checker

A VIPR `RTP infeas` certificate is, in essence, a proof by cases: `lin` leaves
refute LP branches, and `uns` splits combine the branches of an integer variable.
We model that directly as a refutation *tree* — the tree structure carries the
case-split ("assumption") bookkeeping, so a leaf's rows are exactly the branch bounds
accumulated on the path to it. This is complete for MILP infeasibility using only
`lin` (Farkas) leaves and integer `split`s; `rnd` cuts are an optimization layered on
top later. -/

/-- A branch-and-bound refutation: a direct Farkas combination refuting the current
rows (`leaf`), or an integer split on variable `i` at `k` with refutations of both
branches `x_i ≤ k` and `x_i ≥ k+1` (`split`). -/
inductive RefTree where
  | leaf (comb : List (ℚ × Le))
  | split (i : Nat) (k : ℤ) (lo hi : RefTree)
  | derive (comb : List (ℚ × Le)) (rnd : Bool) (sub : RefTree)

/-- The row a `derive` node introduces: the nonnegative combination `combine comb`,
optionally with its right-hand side rounded down (a `rnd`/cut step). -/
def deriveRow (comb : List (ℚ × Le)) (rnd : Bool) : Le :=
  if rnd then ⟨combineForm comb, ((⌊(combine comb).rhs⌋ : ℤ) : ℚ)⟩ else combine comb

/-- Decidable "is an integer" for `ℚ`. -/
def isIntValB (q : ℚ) : Bool := q.den == 1

theorem isIntValB_sound {q : ℚ} (h : isIntValB q = true) : IsIntVal q := by
  have hden : q.den = 1 := by simp only [isIntValB, beq_iff_eq] at h; exact h
  have key : ((q.num : ℤ) : ℚ) = q := by
    have hnd := Rat.num_div_den q
    rw [hden] at hnd
    simpa using hnd
  exact ⟨q.num, key.symm⟩

/-- Validity of a refutation tree against a row set and an integrality predicate.
`leaf comb`: nonnegative multipliers on rows drawn from `rows`, whose combination
cancels identically and has negative constant. `split i k lo hi`: `i` is
integer-constrained and each branch refutes `rows` extended with its bound. -/
def RefTree.Valid (isInt : Nat → Prop) : List Le → RefTree → Prop
  | rows, .leaf comb =>
      (∀ p ∈ comb, 0 ≤ p.1) ∧ (∀ p ∈ comb, p.2 ∈ rows) ∧
      (∀ a, (comb.map (fun p => p.1 * p.2.form.eval a)).sum = 0) ∧
      ((comb.map (fun p => p.1 * p.2.rhs)).sum < 0)
  | rows, .split i k lo hi =>
      isInt i ∧
      RefTree.Valid isInt (leLower i (k : ℚ) :: rows) lo ∧
      RefTree.Valid isInt (leUpper i (k : ℚ) :: rows) hi
  | rows, .derive comb rnd sub =>
      (∀ p ∈ comb, 0 ≤ p.1) ∧ (∀ p ∈ comb, p.2 ∈ rows) ∧
      (rnd = true → ∀ t ∈ combineForm comb, IsIntVal t.coeff ∧ isInt t.idx) ∧
      RefTree.Valid isInt (deriveRow comb rnd :: rows) sub

/-- **The proof-by-cases checker is sound.** A valid refutation tree witnesses that no
valuation whose integer-constrained variables are integral can satisfy `rows` — i.e.
the MILP is infeasible. Leaves are discharged by `farkas_le`, splits by the
exhaustiveness of the integer split (`int_split`). -/
theorem refTree_sound (isInt : Nat → Prop) :
    ∀ (rows : List Le) (t : RefTree), RefTree.Valid isInt rows t →
      ∀ a, (∀ j, isInt j → IsIntVal (a j)) → (∀ c ∈ rows, Le.sat c a) → False := by
  intro rows t
  induction t generalizing rows with
  | leaf comb =>
      intro hval a _ hrows
      obtain ⟨hnn, hused, hcancel, hneg⟩ := hval
      exact farkas_le comb a hnn (hcancel a) hneg (fun p hp => hrows p.2 (hused p hp))
  | split i k lo hi ihlo ihhi =>
      intro hval a hint hrows
      obtain ⟨hIsInt, hvlo, hvhi⟩ := hval
      obtain ⟨v, hv⟩ := hint i hIsInt
      rcases int_split a i k v hv with hlo | hhi
      · refine ihlo (leLower i (k : ℚ) :: rows) hvlo a hint ?_
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact (sat_leLower a i (k : ℚ)).mpr hlo
        · exact hrows c hc
      · refine ihhi (leUpper i (k : ℚ) :: rows) hvhi a hint ?_
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact (sat_leUpper a i (k : ℚ)).mpr hhi
        · exact hrows c hc
  | derive comb rnd sub ihsub =>
      intro hval a hint hrows
      obtain ⟨hnn, hused, hIntCond, hvsub⟩ := hval
      have hlin : Le.sat (combine comb) a :=
        lin_sound comb a hnn (fun p hp => hrows p.2 (hused p hp))
      have hd : Le.sat (deriveRow comb rnd) a := by
        cases rnd with
        | false => simpa [deriveRow] using hlin
        | true =>
            have hInt : IsIntVal ((combineForm comb).eval a) :=
              LinForm.eval_isInt (combineForm comb) a
                (fun t ht => ⟨(hIntCond rfl t ht).1, hint _ (hIntCond rfl t ht).2⟩)
            have hr := rnd_sound (combineForm comb) (combine comb).rhs a hInt hlin
            simpa [deriveRow] using hr
      refine ihsub (deriveRow comb rnd :: rows) hvsub a hint ?_
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact hd
      · exact hrows c hc

/-! ## Step 2: a computable (`Bool`) checker

The one non-decidable part of `RefTree.Valid` is a leaf's *identical cancellation*
`∀ a, (Σ yᵢ · cᵢ.form)(a) = 0`. We make it computable: normalize the combined form to
per-index coefficient sums (`normForm`) and check they all vanish (`formIsZero`),
proving that this implies the form is identically zero. Everything else is decidable,
giving a `Bool` checker `checkRefTree` that runs on a certificate. -/

/-- Value of a per-index coefficient association list at `a`. -/
def evalAL (al : List (Nat × ℚ)) (a : Valuation) : ℚ := (al.map (fun p => p.2 * a p.1)).sum

@[simp] theorem evalAL_nil (a : Valuation) : evalAL [] a = 0 := rfl
@[simp] theorem evalAL_cons (p : Nat × ℚ) (tl : List (Nat × ℚ)) (a : Valuation) :
    evalAL (p :: tl) a = p.2 * a p.1 + evalAL tl a := by simp [evalAL]

/-- Accumulate `(i, c)` into a per-index coefficient association list. -/
def addTerm : List (Nat × ℚ) → Nat → ℚ → List (Nat × ℚ)
  | [], i, c => [(i, c)]
  | (j, d) :: rest, i, c => if i == j then (j, d + c) :: rest else (j, d) :: addTerm rest i c

theorem addTerm_eval (al : List (Nat × ℚ)) (i : Nat) (c : ℚ) (a : Valuation) :
    evalAL (addTerm al i c) a = evalAL al a + c * a i := by
  induction al with
  | nil => simp [addTerm]
  | cons hd tl ih =>
      obtain ⟨j, d⟩ := hd
      by_cases heq : i = j
      · subst heq
        simp only [addTerm, beq_self_eq_true, if_true, evalAL_cons]; ring
      · have hcond : ¬ ((i == j) = true) := by rw [beq_iff_eq]; exact heq
        simp only [addTerm, if_neg hcond, evalAL_cons, ih]; ring

/-- Normalize a linear form to per-index coefficient sums. -/
def normForm (f : LinForm) : List (Nat × ℚ) :=
  f.foldl (fun acc t => addTerm acc t.idx t.coeff) []

theorem normForm_foldl_eval (f : LinForm) (al : List (Nat × ℚ)) (a : Valuation) :
    evalAL (f.foldl (fun acc t => addTerm acc t.idx t.coeff) al) a
      = evalAL al a + f.eval a := by
  induction f generalizing al with
  | nil => simp [LinForm.eval]
  | cons t ts ih =>
      simp only [List.foldl_cons]
      rw [ih (addTerm al t.idx t.coeff), addTerm_eval]
      have : LinForm.eval (t :: ts) a = t.coeff * a t.idx + LinForm.eval ts a := by
        simp [LinForm.eval]
      rw [this]; ring

theorem normForm_eval (f : LinForm) (a : Valuation) : evalAL (normForm f) a = f.eval a := by
  have h := normForm_foldl_eval f [] a
  simpa [normForm] using h

theorem evalAL_zero_of_all (al : List (Nat × ℚ)) (a : Valuation)
    (h : ∀ p ∈ al, p.2 = 0) : evalAL al a = 0 := by
  induction al with
  | nil => simp
  | cons p tl ih =>
      simp only [evalAL_cons, h p (by simp), ih (fun q hq => h q (by simp [hq]))]
      simp

/-- A linear form is identically zero if all its normalized coefficients vanish. -/
def formIsZero (f : LinForm) : Bool := (normForm f).all (fun p => p.2 == 0)

theorem formIsZero_sound (f : LinForm) (h : formIsZero f = true) (a : Valuation) :
    f.eval a = 0 := by
  rw [← normForm_eval]
  refine evalAL_zero_of_all _ a (fun p hp => ?_)
  have := (List.all_eq_true.mp h) p hp
  exact eq_of_beq this

/-- Leaf check: nonnegative multipliers on rows drawn from `rows`, combination cancels
identically (`formIsZero`), and negative constant. -/
def checkLeaf (rows : List Le) (comb : List (ℚ × Le)) : Bool :=
  comb.all (fun p => decide (0 ≤ p.1) && decide (p.2 ∈ rows)) &&
  formIsZero (combineForm comb) &&
  decide ((combine comb).rhs < 0)

/-- The automatic refutation-tree checker (`Bool`). -/
def checkRefTree (isInt : Nat → Bool) : List Le → RefTree → Bool
  | rows, .leaf comb => checkLeaf rows comb
  | rows, .split i k lo hi =>
      isInt i && checkRefTree isInt (leLower i (k : ℚ) :: rows) lo &&
      checkRefTree isInt (leUpper i (k : ℚ) :: rows) hi
  | rows, .derive comb rnd sub =>
      comb.all (fun p => decide (0 ≤ p.1) && decide (p.2 ∈ rows)) &&
      (!rnd || (combineForm comb).all (fun t => isIntValB t.coeff && isInt t.idx)) &&
      checkRefTree isInt (deriveRow comb rnd :: rows) sub

/-- `checkRefTree` implies `RefTree.Valid`. -/
theorem checkRefTree_valid (isInt : Nat → Bool) :
    ∀ (rows : List Le) (t : RefTree), checkRefTree isInt rows t = true →
      RefTree.Valid (fun i => isInt i = true) rows t := by
  intro rows t
  induction t generalizing rows with
  | leaf comb =>
      intro h
      simp only [checkRefTree, checkLeaf, Bool.and_eq_true, List.all_eq_true,
        decide_eq_true_eq] at h
      obtain ⟨⟨hall, hz⟩, hneg⟩ := h
      exact ⟨fun p hp => (hall p hp).1, fun p hp => (hall p hp).2,
             fun a => by rw [← eval_combineForm]; exact formIsZero_sound _ hz a, hneg⟩
  | split i k lo hi ihlo ihhi =>
      intro h
      simp only [checkRefTree, Bool.and_eq_true] at h
      obtain ⟨⟨hi_int, hlo⟩, hhi⟩ := h
      exact ⟨hi_int, ihlo _ hlo, ihhi _ hhi⟩
  | derive comb rnd sub ihsub =>
      intro h
      simp only [checkRefTree, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
        Bool.or_eq_true, Bool.not_eq_true'] at h
      obtain ⟨⟨hall, hint⟩, hsub⟩ := h
      refine ⟨fun p hp => (hall p hp).1, fun p hp => (hall p hp).2, ?_, ihsub _ hsub⟩
      intro hrnd t ht
      rcases hint with hf | hall2
      · exact absurd hrnd (by rw [hf]; simp)
      · exact ⟨isIntValB_sound (hall2 t ht).1, (hall2 t ht).2⟩

/-- **The automatic checker is sound.**  If `checkRefTree` accepts, no valuation whose
integer-constrained variables are integral satisfies `rows` — the MILP is infeasible. -/
theorem checkRefTree_sound (isInt : Nat → Bool) (rows : List Le) (t : RefTree)
    (h : checkRefTree isInt rows t = true) :
    ∀ a, (∀ j, isInt j = true → IsIntVal (a j)) → (∀ c ∈ rows, Le.sat c a) → False :=
  refTree_sound (fun i => isInt i = true) rows t (checkRefTree_valid isInt rows t h)

end AptpCheck.Cert
