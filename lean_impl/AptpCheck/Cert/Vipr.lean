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

end AptpCheck.Cert
