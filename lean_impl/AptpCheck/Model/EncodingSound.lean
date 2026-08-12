import Mathlib
import AptpCheck.Model.Network
import AptpCheck.Model.Encoding
import AptpCheck.Cert.LinCon
import AptpCheck.Coverage.Tautology
import AptpCheck.Pipeline.Affine

/-!
# Encoding over-approximation soundness (proof-oriented encoder)

This module proves the `encoding_overapprox` theorem of DESIGN §4 for a clean,
proof-oriented encoder built by structural recursion so that the emitted MILP rows
and the real network trace stay in sync.

Two results, both kernel-checked and axiom-clean:

* **One hidden layer** (`encoding_overapprox_oneHidden` / `certified_sound_oneHidden`):
  the class `Linear → ReLU → Linear`, the smallest non-affine instance.

* **General arbitrary-depth MLP** (`encoding_overapprox_mlp` / `certified_sound_mlp`,
  and the `satLeaf`-flavoured `certified_sound_mlp_satLeaf`): the dimension-indexed type
  `MLP` = `Linear → ReLU → Linear → ReLU → … → Linear` (a `Linear`, then zero or more
  `(ReLU, Linear)` blocks). This is the standard MLP normal form — `Flatten` is the
  identity on vectors and is elided; Conv is out of scope. Proved by structural induction
  over depth, maintaining the invariant that (a) the trace agrees with the id numbering,
  (b) interval bounds chain layer-to-layer, and (c) rows so far are satisfied.

The encoder emits, for input box `[lo,hi]` and leaf `L`:

* box rows `lo ≤ x ≤ hi`;
* affine-equality rows for each `Linear` layer (`pre = W x + b`);
* the four big-M ReLU rows per hidden neuron, with exact interval bounds;
* the leaf sign rows for neurons the leaf fixes (`pre ≥ 0` / `pre ≤ 0`);
* the objective row `Σ_k c_k · out_k`.

Each theorem exhibits the real trace valuation, shows it satisfies every emitted row and
evaluates the objective to `c · net(x)`; composed with `refute_of_cert` this yields
per-leaf refutation. Everything reuses the two cornerstones `reluRows`/`reluRows_sat`
and `affine_interval_sound` from `Model/Encoding`.
-/

namespace AptpCheck.Model

open AptpCheck.Cert AptpCheck.Coverage

/-! ## The trace valuation and its routing lemmas -/

/-- The real-trace valuation for a one-hidden-layer network.  Variable ids are laid
out as five contiguous blocks: inputs `[0,n0)`, pre-activations `[n0,n0+n1)`,
post-activations `[n0+n1,n0+2n1)`, binaries `[n0+2n1,n0+3n1)`, outputs
`[n0+3n1,n0+3n1+n2)`. -/
def traceVal (n0 n1 n2 : ℕ)
    (xf : Fin n0 → ℚ) (pref postf binf : Fin n1 → ℚ) (outf : Fin n2 → ℚ) : Valuation :=
  fun m =>
    if h0 : m < n0 then xf ⟨m, h0⟩
    else if h1 : m < n0 + n1 then pref ⟨m - n0, by omega⟩
    else if h2 : m < n0 + n1 + n1 then postf ⟨m - (n0 + n1), by omega⟩
    else if h3 : m < n0 + n1 + n1 + n1 then binf ⟨m - (n0 + n1 + n1), by omega⟩
    else if _h4 : m < n0 + n1 + n1 + n1 + n2 then outf ⟨m - (n0 + n1 + n1 + n1), by omega⟩
    else 0

variable {n0 n1 n2 : ℕ}
  {xf : Fin n0 → ℚ} {pref postf binf : Fin n1 → ℚ} {outf : Fin n2 → ℚ}

@[simp] lemma traceVal_x (j : Fin n0) :
    traceVal n0 n1 n2 xf pref postf binf outf j.val = xf j := by
  simp only [traceVal, dif_pos j.isLt]

@[simp] lemma traceVal_pre (i : Fin n1) :
    traceVal n0 n1 n2 xf pref postf binf outf (n0 + i.val) = pref i := by
  have e0 : ¬ (n0 + i.val < n0) := by omega
  have e1 : n0 + i.val < n0 + n1 := by omega
  simp only [traceVal, dif_neg e0, dif_pos e1]
  congr 1
  apply Fin.ext
  simp only []
  omega

@[simp] lemma traceVal_post (i : Fin n1) :
    traceVal n0 n1 n2 xf pref postf binf outf (n0 + n1 + i.val) = postf i := by
  have e0 : ¬ (n0 + n1 + i.val < n0) := by omega
  have e1 : ¬ (n0 + n1 + i.val < n0 + n1) := by omega
  have e2 : n0 + n1 + i.val < n0 + n1 + n1 := by omega
  simp only [traceVal, dif_neg e0, dif_neg e1, dif_pos e2]
  congr 1
  apply Fin.ext
  simp only []
  omega

@[simp] lemma traceVal_bin (i : Fin n1) :
    traceVal n0 n1 n2 xf pref postf binf outf (n0 + n1 + n1 + i.val) = binf i := by
  have e0 : ¬ (n0 + n1 + n1 + i.val < n0) := by omega
  have e1 : ¬ (n0 + n1 + n1 + i.val < n0 + n1) := by omega
  have e2 : ¬ (n0 + n1 + n1 + i.val < n0 + n1 + n1) := by omega
  have e3 : n0 + n1 + n1 + i.val < n0 + n1 + n1 + n1 := by omega
  simp only [traceVal, dif_neg e0, dif_neg e1, dif_neg e2, dif_pos e3]
  congr 1
  apply Fin.ext
  simp only []
  omega

@[simp] lemma traceVal_out (k : Fin n2) :
    traceVal n0 n1 n2 xf pref postf binf outf (n0 + n1 + n1 + n1 + k.val) = outf k := by
  have e0 : ¬ (n0 + n1 + n1 + n1 + k.val < n0) := by omega
  have e1 : ¬ (n0 + n1 + n1 + n1 + k.val < n0 + n1) := by omega
  have e2 : ¬ (n0 + n1 + n1 + n1 + k.val < n0 + n1 + n1) := by omega
  have e3 : ¬ (n0 + n1 + n1 + n1 + k.val < n0 + n1 + n1 + n1) := by omega
  have e4 : n0 + n1 + n1 + n1 + k.val < n0 + n1 + n1 + n1 + n2 := by omega
  simp only [traceVal, dif_neg e0, dif_neg e1, dif_neg e2, dif_neg e3, dif_pos e4]
  congr 1
  apply Fin.ext
  simp only []
  omega

/-! ## Generic row constructors and their satisfaction -/

/-- Evaluate a form `⟨p,coef⟩ :: [⟨idx j, cf j⟩ | j]` (a head term plus a `Fin`-indexed
tail). -/
lemma eval_consOfFn {m : ℕ} (p : Nat) (coef : ℚ) (idx : Fin m → Nat) (cf : Fin m → ℚ)
    (a : Valuation) :
    LinForm.eval (⟨p, coef⟩ :: List.ofFn (fun j => (⟨idx j, cf j⟩ : Term))) a
      = coef * a p + ∑ j, cf j * a (idx j) := by
  simp only [LinForm.eval, List.map_cons, List.sum_cons, List.map_ofFn, List.sum_ofFn,
    Function.comp]

/-- Affine-equality rows encoding `v[p] = (Σ_j w_j · v[idx j]) + b` as two `≤` rows. -/
def affEqRows {m : ℕ} (p : Nat) (idx : Fin m → Nat) (w : Fin m → ℚ) (b : ℚ) : List Le :=
  [ ⟨⟨p, 1⟩ :: List.ofFn (fun j => (⟨idx j, -(w j)⟩ : Term)), b⟩,
    ⟨⟨p, -1⟩ :: List.ofFn (fun j => (⟨idx j, w j⟩ : Term)), -b⟩ ]

/-- The real trace satisfies the affine-equality rows exactly. -/
lemma affEqRows_sat {m : ℕ} (p : Nat) (idx : Fin m → Nat) (w : Fin m → ℚ) (b : ℚ)
    (a : Valuation) (heq : a p = (∑ j, w j * a (idx j)) + b) :
    ∀ r ∈ affEqRows p idx w b, Le.sat r a := by
  have hsum : (∑ j, w j * a (idx j)) = a p - b := by rw [heq]; ring
  intro r hr
  simp only [affEqRows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · -- row A:  a p - Σ w·v ≤ b
    simp only [Le.sat, eval_consOfFn, neg_mul, Finset.sum_neg_distrib]
    linarith [hsum]
  · -- row B:  -(a p) + Σ w·v ≤ -b
    simp only [Le.sat, eval_consOfFn]
    linarith [hsum]

/-- Leaf sign rows for a neuron: `pre ≥ 0` if the leaf fixes it active, `pre ≤ 0` if
fixed inactive (nothing if free). -/
def leafRows (L : List Int) (gid preId : Nat) : List Le :=
  (if (↑gid : Int) ∈ L then [(⟨[⟨preId, -1⟩], 0⟩ : Le)] else []) ++
  (if (-(↑gid) : Int) ∈ L then [(⟨[⟨preId, 1⟩], 0⟩ : Le)] else [])

/-- The real trace satisfies the leaf sign rows, given consistency of the pre-activation
sign with each fixed literal. -/
lemma leafRows_sat (L : List Int) (gid preId : Nat) (a : Valuation)
    (hact : (↑gid : Int) ∈ L → 0 ≤ a preId)
    (hinact : (-(↑gid) : Int) ∈ L → a preId ≤ 0) :
    ∀ r ∈ leafRows L gid preId, Le.sat r a := by
  intro r hr
  simp only [leafRows, List.mem_append] at hr
  rcases hr with hr | hr
  · by_cases hc : (↑gid : Int) ∈ L
    · rw [if_pos hc, List.mem_singleton] at hr
      subst hr
      simp only [Le.sat, LinForm.eval, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, add_zero, neg_one_mul]
      linarith [hact hc]
    · rw [if_neg hc] at hr; exact absurd hr (by simp)
  · by_cases hc : (-(↑gid) : Int) ∈ L
    · rw [if_pos hc, List.mem_singleton] at hr
      subst hr
      simp only [Le.sat, LinForm.eval, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, add_zero, one_mul]
      linarith [hinact hc]
    · rw [if_neg hc] at hr; exact absurd hr (by simp)

/-! ## Network signal values for one hidden layer -/

/-- Pre-activation of hidden neuron `i`: `Σ_j W₁[i,j] x_j + b₁ i`. -/
def preAct {n0 n1 : ℕ} (W1 : Fin n1 → Fin n0 → ℚ) (b1 : Fin n1 → ℚ) (x : Fin n0 → ℚ)
    (i : Fin n1) : ℚ := (∑ j, W1 i j * x j) + b1 i

/-- Post-activation of hidden neuron `i`: `max (pre i) 0`. -/
def postAct {n0 n1 : ℕ} (W1 : Fin n1 → Fin n0 → ℚ) (b1 : Fin n1 → ℚ) (x : Fin n0 → ℚ)
    (i : Fin n1) : ℚ := max (preAct W1 b1 x i) 0

/-- Binary indicator of hidden neuron `i`: `1` iff active. -/
def binAct {n0 n1 : ℕ} (W1 : Fin n1 → Fin n0 → ℚ) (b1 : Fin n1 → ℚ) (x : Fin n0 → ℚ)
    (i : Fin n1) : ℚ := if 0 ≤ preAct W1 b1 x i then 1 else 0

/-- Output `k`: `Σ_i W₂[k,i] · post_i + b₂ k`. -/
def outAct {n1 n2 : ℕ} (W2 : Fin n2 → Fin n1 → ℚ) (b2 : Fin n2 → ℚ) (posts : Fin n1 → ℚ)
    (k : Fin n2) : ℚ := (∑ i, W2 k i * posts i) + b2 k

/-- Exact interval lower bound of the pre-activation of neuron `i` (`W⁺·lo + W⁻·hi + b`). -/
def lbAff {n0 n1 : ℕ} (W1 : Fin n1 → Fin n0 → ℚ) (b1 : Fin n1 → ℚ) (lo hi : Fin n0 → ℚ)
    (i : Fin n1) : ℚ := (∑ j, (max (W1 i j) 0 * lo j + min (W1 i j) 0 * hi j)) + b1 i

/-- Exact interval upper bound of the pre-activation of neuron `i` (`W⁺·hi + W⁻·lo + b`). -/
def ubAff {n0 n1 : ℕ} (W1 : Fin n1 → Fin n0 → ℚ) (b1 : Fin n1 → ℚ) (lo hi : Fin n0 → ℚ)
    (i : Fin n1) : ℚ := (∑ j, (max (W1 i j) 0 * hi j + min (W1 i j) 0 * lo j)) + b1 i

/-- The true ReLU sign vector at `x`: neuron gid `nn` (1-based) is active iff its
pre-activation is `≥ 0`. -/
def trueSign {n0 n1 : ℕ} (W1 : Fin n1 → Fin n0 → ℚ) (b1 : Fin n1 → ℚ) (x : Fin n0 → ℚ) :
    Nat → Bool :=
  fun nn => if h : 0 < nn ∧ nn ≤ n1 then decide (0 ≤ preAct W1 b1 x ⟨nn - 1, by omega⟩)
            else false

lemma trueSign_succ {n0 n1 : ℕ} (W1 : Fin n1 → Fin n0 → ℚ) (b1 : Fin n1 → ℚ) (x : Fin n0 → ℚ)
    (i : Fin n1) : trueSign W1 b1 x (i.val + 1) = decide (0 ≤ preAct W1 b1 x i) := by
  simp only [trueSign, dif_pos (show 0 < i.val + 1 ∧ i.val + 1 ≤ n1 from ⟨by omega, by omega⟩)]
  have : (⟨i.val + 1 - 1, by omega⟩ : Fin n1) = i :=
    Fin.ext (show i.val + 1 - 1 = i.val by omega)
  rw [this]

/-! ## The one-hidden-layer encoder rows and objective -/

open AptpCheck.Pipeline in
/-- All MILP rows emitted for a one-hidden-layer network `Linear → ReLU → Linear` on the
input box `[lo,hi]` and leaf `L`. -/
def encRowsOneHidden {n0 n1 n2 : ℕ}
    (W1 : Fin n1 → Fin n0 → ℚ) (b1 : Fin n1 → ℚ)
    (W2 : Fin n2 → Fin n1 → ℚ) (b2 : Fin n2 → ℚ)
    (lo hi : Fin n0 → ℚ) (L : List Int) : List Le :=
  boxRows lo hi
  ++ (List.finRange n1).flatMap (fun i =>
        affEqRows (n0 + i.val) (fun j : Fin n0 => j.val) (fun j => W1 i j) (b1 i))
  ++ (List.finRange n1).flatMap (fun i =>
        reluRows (lbAff W1 b1 lo hi i) (ubAff W1 b1 lo hi i)
          (n0 + i.val) (n0 + n1 + i.val) (n0 + n1 + n1 + i.val))
  ++ (List.finRange n1).flatMap (fun i => leafRows L (i.val + 1) (n0 + i.val))
  ++ (List.finRange n2).flatMap (fun k =>
        affEqRows (n0 + n1 + n1 + n1 + k.val)
          (fun i : Fin n1 => n0 + n1 + i.val) (fun i => W2 k i) (b2 k))

/-- The objective row `Σ_k c_k · out_k ≤ rhs` over the terminal output variables. -/
def objRowOneHidden (n0 n1 : ℕ) {n2 : ℕ} (cc : Fin n2 → ℚ) (rhs : ℚ) : Le :=
  ⟨List.ofFn (fun k : Fin n2 => (⟨n0 + n1 + n1 + n1 + k.val, cc k⟩ : Term)), rhs⟩

/-- The real-trace valuation for the one-hidden-layer network at input `x`. -/
def oneHiddenTrace {n0 n1 n2 : ℕ}
    (W1 : Fin n1 → Fin n0 → ℚ) (b1 : Fin n1 → ℚ)
    (W2 : Fin n2 → Fin n1 → ℚ) (b2 : Fin n2 → ℚ) (x : Fin n0 → ℚ) : Valuation :=
  traceVal n0 n1 n2 x (preAct W1 b1 x) (postAct W1 b1 x) (binAct W1 b1 x)
    (outAct W2 b2 (postAct W1 b1 x))

/-! ## Consistency of the leaf with the real signs -/

/-- From `satLeaf`, a fixed-active neuron has `pre ≥ 0` and a fixed-inactive one has
`pre ≤ 0`. -/
lemma sign_of_satLeaf {n0 n1 : ℕ} (W1 : Fin n1 → Fin n0 → ℚ) (b1 : Fin n1 → ℚ)
    (x : Fin n0 → ℚ) (L : List Int) (hL : satLeaf L (trueSign W1 b1 x) = true) (i : Fin n1) :
    ((↑(i.val + 1) : Int) ∈ L → 0 ≤ preAct W1 b1 x i) ∧
    ((-(↑(i.val + 1)) : Int) ∈ L → preAct W1 b1 x i ≤ 0) := by
  simp only [satLeaf, List.all_eq_true] at hL
  refine ⟨fun hmem => ?_, fun hmem => ?_⟩
  · have h := hL _ hmem
    rw [if_pos (by positivity)] at h
    simp only [Int.natAbs_natCast] at h
    rw [trueSign_succ] at h
    exact of_decide_eq_true h
  · have h := hL _ hmem
    rw [if_neg (by omega)] at h
    simp only [Int.natAbs_neg, Int.natAbs_natCast] at h
    rw [trueSign_succ] at h
    simp only [Bool.not_eq_true'] at h
    exact le_of_lt (not_le.mp (of_decide_eq_false h))

/-! ## The over-approximation theorem for one hidden layer -/

open AptpCheck.Pipeline in
/-- The real trace satisfies every emitted row. -/
theorem oneHidden_rows_sat {n0 n1 n2 : ℕ}
    (W1 : Fin n1 → Fin n0 → ℚ) (b1 : Fin n1 → ℚ)
    (W2 : Fin n2 → Fin n1 → ℚ) (b2 : Fin n2 → ℚ)
    (lo hi : Fin n0 → ℚ) (L : List Int)
    (x : Fin n0 → ℚ) (hx : ∀ j, lo j ≤ x j ∧ x j ≤ hi j)
    (hL : satLeaf L (trueSign W1 b1 x) = true) :
    ∀ r ∈ encRowsOneHidden W1 b1 W2 b2 lo hi L, Le.sat r (oneHiddenTrace W1 b1 W2 b2 x) := by
  intro r hr
  simp only [encRowsOneHidden, List.mem_append, List.mem_flatMap] at hr
  rcases hr with ((((hbox | ⟨i, _, hr⟩) | ⟨i, _, hr⟩) | ⟨i, _, hr⟩) | ⟨k, _, hr⟩)
  · -- box rows
    simp only [boxRows, List.mem_append, List.mem_ofFn] at hbox
    rcases hbox with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · simp only [oneHiddenTrace, Le.sat, LinForm.eval, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, one_mul, add_zero, traceVal_x]
      exact (hx j).2
    · simp only [oneHiddenTrace, Le.sat, LinForm.eval, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, neg_one_mul, add_zero, traceVal_x]
      linarith [(hx j).1]
  · -- Linear₁ affine equalities
    refine affEqRows_sat (n0 + i.val) (fun j : Fin n0 => j.val) (fun j => W1 i j) (b1 i)
      _ ?_ r hr
    simp only [oneHiddenTrace, traceVal_pre, traceVal_x, preAct]
  · -- big-M ReLU rows
    refine reluRows_sat (lbAff W1 b1 lo hi i) (ubAff W1 b1 lo hi i)
      (n0 + i.val) (n0 + n1 + i.val) (n0 + n1 + n1 + i.val) _ ?_ ?_ ?_ ?_ r hr
    · rw [oneHiddenTrace, traceVal_pre]
      exact (affine_interval_sound (W1 i) x lo hi (b1 i)
        (fun j => (hx j).1) (fun j => (hx j).2)).1
    · rw [oneHiddenTrace, traceVal_pre]
      exact (affine_interval_sound (W1 i) x lo hi (b1 i)
        (fun j => (hx j).1) (fun j => (hx j).2)).2
    · simp only [oneHiddenTrace, traceVal_post, traceVal_pre, postAct]
    · simp only [oneHiddenTrace, traceVal_bin, traceVal_pre, binAct]
  · -- leaf sign rows
    refine leafRows_sat L (i.val + 1) (n0 + i.val) _ ?_ ?_ r hr
    · intro hmem
      rw [oneHiddenTrace, traceVal_pre]
      exact (sign_of_satLeaf W1 b1 x L hL i).1 hmem
    · intro hmem
      rw [oneHiddenTrace, traceVal_pre]
      exact (sign_of_satLeaf W1 b1 x L hL i).2 hmem
  · -- Linear₂ affine equalities
    refine affEqRows_sat (n0 + n1 + n1 + n1 + k.val)
      (fun i : Fin n1 => n0 + n1 + i.val) (fun i => W2 k i) (b2 k) _ ?_ r hr
    simp only [oneHiddenTrace, traceVal_out, traceVal_post, outAct]

/-- The objective row evaluates to `c · net(x)` on the real trace. -/
theorem oneHidden_obj_eval {n0 n1 n2 : ℕ}
    (W1 : Fin n1 → Fin n0 → ℚ) (b1 : Fin n1 → ℚ)
    (W2 : Fin n2 → Fin n1 → ℚ) (b2 : Fin n2 → ℚ)
    (cc : Fin n2 → ℚ) (rhs : ℚ) (x : Fin n0 → ℚ) :
    (objRowOneHidden n0 n1 cc rhs).form.eval (oneHiddenTrace W1 b1 W2 b2 x)
      = ∑ k, cc k * outAct W2 b2 (postAct W1 b1 x) k := by
  simp only [oneHiddenTrace, objRowOneHidden, LinForm.eval, List.map_ofFn, List.sum_ofFn,
    Function.comp, traceVal_out]

open AptpCheck.Pipeline in
/-- **Encoding over-approximation for one hidden layer.** For any input `x` in the box
whose true ReLU signs are consistent with the leaf `L`, the real trace valuation is a
feasible point of every emitted MILP row, and the objective evaluates to `c · net(x)`. -/
theorem encoding_overapprox_oneHidden {n0 n1 n2 : ℕ}
    (W1 : Fin n1 → Fin n0 → ℚ) (b1 : Fin n1 → ℚ)
    (W2 : Fin n2 → Fin n1 → ℚ) (b2 : Fin n2 → ℚ)
    (cc : Fin n2 → ℚ) (rhs : ℚ) (lo hi : Fin n0 → ℚ) (L : List Int)
    (x : Fin n0 → ℚ) (hx : ∀ j, lo j ≤ x j ∧ x j ≤ hi j)
    (hL : satLeaf L (trueSign W1 b1 x) = true) :
    ∃ a : Valuation,
      (∀ r ∈ encRowsOneHidden W1 b1 W2 b2 lo hi L, Le.sat r a) ∧
      (objRowOneHidden n0 n1 cc rhs).form.eval a
        = ∑ k, cc k * outAct W2 b2 (postAct W1 b1 x) k :=
  ⟨oneHiddenTrace W1 b1 W2 b2 x,
   oneHidden_rows_sat W1 b1 W2 b2 lo hi L x hx hL,
   oneHidden_obj_eval W1 b1 W2 b2 cc rhs x⟩

open AptpCheck.Pipeline in
/-- **Per-leaf refutation for one hidden layer.** A Farkas certificate that refutes the
emitted rows together with the negated objective proves the property `c · net(x) > rhs`
for every `x` in the box consistent with the leaf. -/
theorem certified_sound_oneHidden {n0 n1 n2 : ℕ}
    (W1 : Fin n1 → Fin n0 → ℚ) (b1 : Fin n1 → ℚ)
    (W2 : Fin n2 → Fin n1 → ℚ) (b2 : Fin n2 → ℚ)
    (cc : Fin n2 → ℚ) (rhs : ℚ) (lo hi : Fin n0 → ℚ) (L : List Int)
    (x : Fin n0 → ℚ) (hx : ∀ j, lo j ≤ x j ∧ x j ≤ hi j)
    (hL : satLeaf L (trueSign W1 b1 x) = true)
    (comb : List (ℚ × Le))
    (hsub : ∀ p ∈ comb,
      p.2 ∈ (objRowOneHidden n0 n1 cc rhs :: encRowsOneHidden W1 b1 W2 b2 lo hi L))
    (hnn : ∀ p ∈ comb, 0 ≤ p.1)
    (hcancel : (comb.map (fun p =>
        p.1 * p.2.form.eval (oneHiddenTrace W1 b1 W2 b2 x))).sum = 0)
    (hneg : (comb.map (fun p => p.1 * p.2.rhs)).sum < 0) :
    rhs < ∑ k, cc k * outAct W2 b2 (postAct W1 b1 x) k := by
  have h := refute_of_cert (encRowsOneHidden W1 b1 W2 b2 lo hi L) (objRowOneHidden n0 n1 cc rhs)
    (oneHiddenTrace W1 b1 W2 b2 x) comb hsub hnn hcancel hneg
    (oneHidden_rows_sat W1 b1 W2 b2 lo hi L x hx hL)
  rw [oneHidden_obj_eval W1 b1 W2 b2 cc rhs x] at h
  exact h

/-! # General arbitrary-depth MLP

We now generalise to an arbitrary-depth MLP: `Linear → ReLU → Linear → ReLU → … → Linear`
(a Linear, then zero or more `(ReLU, Linear)` blocks). This is the standard MLP normal
form (`Flatten` is the identity on vectors, so it is elided). We model it with a
dimension-indexed inductive type and prove `encoding_overapprox`/`certified_sound` by
structural induction over its depth. -/

/-- An MLP with input dimension `inD` and output dimension `outD`. `last W b` is a
terminal affine layer `Wx+b`; `cons W b rest` is an affine layer followed by `ReLU` and
then the sub-network `rest`. -/
inductive MLP : ℕ → ℕ → Type where
  | last {inD outD : ℕ} (W : Fin outD → Fin inD → ℚ) (b : Fin outD → ℚ) : MLP inD outD
  | cons {inD hidD outD : ℕ} (W : Fin hidD → Fin inD → ℚ) (b : Fin hidD → ℚ)
      (rest : MLP hidD outD) : MLP inD outD

/-- Exact forward evaluation of an MLP. -/
def MLP.eval : {inD outD : ℕ} → MLP inD outD → (Fin inD → ℚ) → (Fin outD → ℚ)
  | _, _, .last W b, x => fun i => preAct W b x i
  | _, _, .cons W b rest, x => rest.eval (postAct W b x)

/-- The list of trace values *allocated* by the sub-network (excluding its input block),
in id order. For `last`: the output block. For `cons`: pre-, binary-, post-blocks, then
the recursive blocks of `rest` (whose input block is the post-block). -/
def MLP.blocks : {inD outD : ℕ} → MLP inD outD → (Fin inD → ℚ) → List ℚ
  | _, _, .last W b, x => List.ofFn (fun i => preAct W b x i)
  | _, _, .cons W b rest, x =>
      List.ofFn (preAct W b x) ++ List.ofFn (binAct W b x) ++ List.ofFn (postAct W b x)
        ++ MLP.blocks rest (postAct W b x)

/-- Number of trace ids the sub-network allocates (`= (blocks _).length`). -/
def MLP.size : {inD outD : ℕ} → MLP inD outD → ℕ
  | _, outD, .last _ _ => outD
  | _, _, .cons (hidD := hidD) _ _ rest => hidD + hidD + hidD + rest.size

lemma MLP.length_blocks : ∀ {inD outD : ℕ} (net : MLP inD outD) (x : Fin inD → ℚ),
    (net.blocks x).length = net.size
  | _, _, .last W b, x => by simp [MLP.blocks, MLP.size]
  | _, _, .cons W b rest, x => by
      simp only [MLP.blocks, MLP.size, List.length_append, List.length_ofFn,
        MLP.length_blocks rest]

/-- Absolute id of the output block, given the input block starts at `inBase`. -/
def MLP.outBase : {inD outD : ℕ} → MLP inD outD → ℕ → ℕ
  | inD, _, .last _ _, inBase => inBase + inD
  | inD, _, .cons (hidD := hidD) _ _ rest, inBase => rest.outBase (inBase + inD + hidD + hidD)

/-- The full trace value list: input block followed by all allocated blocks. -/
def MLP.traceList {inD outD : ℕ} (net : MLP inD outD) (x : Fin inD → ℚ) : List ℚ :=
  List.ofFn x ++ net.blocks x

/-- The real-trace valuation (id ↦ value); ids are positions in `traceList`. -/
def MLP.trace {inD outD : ℕ} (net : MLP inD outD) (x : Fin inD → ℚ) : Valuation :=
  fun n => (net.traceList x).getD n 0

/-! ## List-level access lemmas -/

private lemma getD_ofFn {m : ℕ} (f : Fin m → ℚ) (i : Fin m) :
    (List.ofFn f).getD i.val 0 = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [Fin.eta]

/-- Input-block value: id `j` of `traceList` holds `x j`. -/
lemma MLP.traceList_input {inD outD : ℕ} (net : MLP inD outD) (x : Fin inD → ℚ)
    (j : Fin inD) : (net.traceList x).getD j.val 0 = x j := by
  unfold MLP.traceList
  rw [List.getD_append _ _ _ _ (by rw [List.length_ofFn]; exact j.isLt), getD_ofFn]

/-- `traceList (cons …)` splits as input‖pre‖bin prefix, then `rest`'s trace list. -/
lemma MLP.traceList_cons {inD hidD outD : ℕ}
    (W : Fin hidD → Fin inD → ℚ) (b : Fin hidD → ℚ) (rest : MLP hidD outD)
    (x : Fin inD → ℚ) :
    (MLP.cons W b rest).traceList x
      = (List.ofFn x ++ List.ofFn (preAct W b x) ++ List.ofFn (binAct W b x))
        ++ rest.traceList (postAct W b x) := by
  simp only [MLP.traceList, MLP.blocks, List.append_assoc]

/-- Pre-block value: id `inD + i` holds the pre-activation `pre i`. -/
lemma MLP.traceList_cons_pre {inD hidD outD : ℕ}
    (W : Fin hidD → Fin inD → ℚ) (b : Fin hidD → ℚ) (rest : MLP hidD outD)
    (x : Fin inD → ℚ) (i : Fin hidD) :
    ((MLP.cons W b rest).traceList x).getD (inD + i.val) 0 = preAct W b x i := by
  rw [MLP.traceList_cons, List.getD_append, List.getD_append, List.getD_append_right,
    List.length_ofFn, Nat.add_sub_cancel_left]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]; simp [Fin.eta]
  · rw [List.length_ofFn]; omega
  · simp only [List.length_append, List.length_ofFn]; omega
  · simp only [List.length_append, List.length_ofFn]; omega

/-- Binary-block value: id `inD + hidD + i` holds the indicator `bin i`. -/
lemma MLP.traceList_cons_bin {inD hidD outD : ℕ}
    (W : Fin hidD → Fin inD → ℚ) (b : Fin hidD → ℚ) (rest : MLP hidD outD)
    (x : Fin inD → ℚ) (i : Fin hidD) :
    ((MLP.cons W b rest).traceList x).getD (inD + hidD + i.val) 0 = binAct W b x i := by
  rw [MLP.traceList_cons, List.getD_append, List.getD_append_right,
    show (List.ofFn x ++ List.ofFn (preAct W b x)).length = inD + hidD by
      simp only [List.length_append, List.length_ofFn],
    show inD + hidD + i.val - (inD + hidD) = i.val by omega]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]; simp [Fin.eta]
  · simp only [List.length_append, List.length_ofFn]; omega
  · simp only [List.length_append, List.length_ofFn]; omega

/-- Delegation: ids `≥ inD + hidD + hidD` of `traceList (cons …)` match `rest`'s trace
list (whose input block is the post-block). -/
lemma MLP.traceList_cons_delegate {inD hidD outD : ℕ}
    (W : Fin hidD → Fin inD → ℚ) (b : Fin hidD → ℚ) (rest : MLP hidD outD)
    (x : Fin inD → ℚ) (m : ℕ) :
    ((MLP.cons W b rest).traceList x).getD (inD + hidD + hidD + m) 0
      = (rest.traceList (postAct W b x)).getD m 0 := by
  rw [MLP.traceList_cons, List.getD_append_right,
    show (List.ofFn x ++ List.ofFn (preAct W b x) ++ List.ofFn (binAct W b x)).length
        = inD + hidD + hidD by simp only [List.length_append, List.length_ofFn],
    Nat.add_sub_cancel_left]
  simp only [List.length_append, List.length_ofFn]; omega

/-- Output-block value for a terminal layer: id `inD + k` holds `eval k = pre k`. -/
lemma MLP.traceList_last_out {inD outD : ℕ}
    (W : Fin outD → Fin inD → ℚ) (b : Fin outD → ℚ) (x : Fin inD → ℚ) (k : Fin outD) :
    ((MLP.last W b).traceList x).getD (inD + k.val) 0 = preAct W b x k := by
  unfold MLP.traceList MLP.blocks
  rw [List.getD_append_right, List.length_ofFn, Nat.add_sub_cancel_left]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]; simp [Fin.eta]
  · rw [List.length_ofFn]; omega

/-! ## Agreement of an abstract valuation with the trace -/

/-- `a` agrees with the sub-network's trace list starting at id `inBase`. -/
def MLP.Agree {inD outD : ℕ} (net : MLP inD outD) (inBase : ℕ) (xv : Fin inD → ℚ)
    (a : Valuation) : Prop :=
  ∀ n, a (inBase + n) = (net.traceList xv).getD n 0

/-- The concrete real trace agrees with itself starting at id `0`. -/
lemma MLP.agree_trace {inD outD : ℕ} (net : MLP inD outD) (x : Fin inD → ℚ) :
    net.Agree 0 x (net.trace x) := by
  intro n; simp only [MLP.trace, Nat.zero_add]

lemma MLP.Agree.input {inD outD : ℕ} {net : MLP inD outD} {inBase : ℕ}
    {xv : Fin inD → ℚ} {a : Valuation} (h : net.Agree inBase xv a) (j : Fin inD) :
    a (inBase + j.val) = xv j := (h j.val).trans (net.traceList_input xv j)

lemma MLP.Agree.consPre {inD hidD outD : ℕ}
    {W : Fin hidD → Fin inD → ℚ} {b : Fin hidD → ℚ} {rest : MLP hidD outD}
    {inBase : ℕ} {xv : Fin inD → ℚ} {a : Valuation}
    (h : (MLP.cons W b rest).Agree inBase xv a) (i : Fin hidD) :
    a (inBase + inD + i.val) = preAct W b xv i := by
  have h1 := h (inD + i.val)
  rw [show inBase + (inD + i.val) = inBase + inD + i.val from by omega] at h1
  rw [h1, MLP.traceList_cons_pre]

lemma MLP.Agree.consBin {inD hidD outD : ℕ}
    {W : Fin hidD → Fin inD → ℚ} {b : Fin hidD → ℚ} {rest : MLP hidD outD}
    {inBase : ℕ} {xv : Fin inD → ℚ} {a : Valuation}
    (h : (MLP.cons W b rest).Agree inBase xv a) (i : Fin hidD) :
    a (inBase + inD + hidD + i.val) = binAct W b xv i := by
  have h1 := h (inD + hidD + i.val)
  rw [show inBase + (inD + hidD + i.val) = inBase + inD + hidD + i.val from by omega] at h1
  rw [h1, MLP.traceList_cons_bin]

/-- The recursive agreement for `rest`: `a` agrees with `rest`'s trace list starting at
the post-block. -/
lemma MLP.Agree.rest {inD hidD outD : ℕ}
    {W : Fin hidD → Fin inD → ℚ} {b : Fin hidD → ℚ} {rest : MLP hidD outD}
    {inBase : ℕ} {xv : Fin inD → ℚ} {a : Valuation}
    (h : (MLP.cons W b rest).Agree inBase xv a) :
    rest.Agree (inBase + inD + hidD + hidD) (postAct W b xv) a := by
  intro m
  have h1 := h (inD + hidD + hidD + m)
  rw [show inBase + (inD + hidD + hidD + m) = inBase + inD + hidD + hidD + m from by omega] at h1
  rw [h1, MLP.traceList_cons_delegate]

lemma MLP.Agree.consPost {inD hidD outD : ℕ}
    {W : Fin hidD → Fin inD → ℚ} {b : Fin hidD → ℚ} {rest : MLP hidD outD}
    {inBase : ℕ} {xv : Fin inD → ℚ} {a : Valuation}
    (h : (MLP.cons W b rest).Agree inBase xv a) (i : Fin hidD) :
    a (inBase + inD + hidD + hidD + i.val) = postAct W b xv i := by
  have hr := h.rest (i.val)
  rw [show inBase + inD + hidD + hidD + i.val = (inBase + inD + hidD + hidD) + i.val from by omega,
    hr, MLP.traceList_input]

lemma MLP.Agree.lastOut {inD outD : ℕ}
    {W : Fin outD → Fin inD → ℚ} {b : Fin outD → ℚ}
    {inBase : ℕ} {xv : Fin inD → ℚ} {a : Valuation}
    (h : (MLP.last W b).Agree inBase xv a) (k : Fin outD) :
    a (inBase + inD + k.val) = preAct W b xv k := by
  have h1 := h (inD + k.val)
  rw [show inBase + (inD + k.val) = inBase + inD + k.val from by omega] at h1
  rw [h1, MLP.traceList_last_out]

/-! ## The recursive encoder, consistency predicate and objective -/

open AptpCheck.Pipeline in
/-- The MILP rows emitted by the sub-network, with input block at id `inBase`, input
bounds `inLo/inHi`, leaf `L`, and neuron-count offset `gid0`. Layout per `cons` block:
pre `[inBase+inD, +hidD)`, binary `[+hidD, +hidD)`, post `[+hidD, +hidD)`, then `rest`. -/
def MLP.encRows : {inD outD : ℕ} → MLP inD outD → ℕ → (Fin inD → ℚ) → (Fin inD → ℚ) →
    List Int → ℕ → List Le
  | inD, outD, .last W b, inBase, _inLo, _inHi, _L, _gid0 =>
      (List.finRange outD).flatMap (fun k =>
        affEqRows (inBase + inD + k.val) (fun j => inBase + j.val) (fun j => W k j) (b k))
  | inD, _outD, .cons (hidD := hidD) W b rest, inBase, inLo, inHi, L, gid0 =>
      (List.finRange hidD).flatMap (fun i =>
        affEqRows (inBase + inD + i.val) (fun j => inBase + j.val) (fun j => W i j) (b i))
      ++ (List.finRange hidD).flatMap (fun i =>
        reluRows (lbAff W b inLo inHi i) (ubAff W b inLo inHi i)
          (inBase + inD + i.val) (inBase + inD + hidD + hidD + i.val)
          (inBase + inD + hidD + i.val))
      ++ (List.finRange hidD).flatMap (fun i =>
        leafRows L (gid0 + i.val + 1) (inBase + inD + i.val))
      ++ rest.encRows (inBase + inD + hidD + hidD)
          (fun i => max (lbAff W b inLo inHi i) 0) (fun i => max (ubAff W b inLo inHi i) 0)
          L (gid0 + hidD)

/-- The leaf is consistent with the real signs: every fixed neuron's real pre-activation
has the sign the leaf claims. `gid0` offsets the global 1-based neuron ids. -/
def MLP.consistent : {inD outD : ℕ} → MLP inD outD → ℕ → (Fin inD → ℚ) → List Int → Prop
  | _, _, .last _ _, _, _, _ => True
  | _, _, .cons (hidD := hidD) W b rest, gid0, xv, L =>
      (∀ i : Fin hidD,
        ((↑(gid0 + i.val + 1) : Int) ∈ L → 0 ≤ preAct W b xv i) ∧
        ((-(↑(gid0 + i.val + 1)) : Int) ∈ L → preAct W b xv i ≤ 0))
      ∧ rest.consistent (gid0 + hidD) (postAct W b xv) L

/-- The objective row `Σ_k c_k · out_k ≤ rhs` over the output block at `net.outBase inBase`. -/
def MLP.objRow {inD outD : ℕ} (net : MLP inD outD) (inBase : ℕ) (cc : Fin outD → ℚ)
    (rhs : ℚ) : Le :=
  ⟨List.ofFn (fun k : Fin outD => (⟨net.outBase inBase + k.val, cc k⟩ : Term)), rhs⟩

/-! ## The main induction: emitted rows are satisfied and the output block is exact -/

/-- **Core induction.** If the input real values `xv` lie in `[inLo,inHi]`, the abstract
valuation `a` agrees with the trace list from `inBase`, and the leaf is consistent, then
`a` satisfies every emitted row and the output block holds the true network output. -/
lemma MLP.encRows_sat_and_out {inD outD : ℕ} (net : MLP inD outD) :
    ∀ (inBase : ℕ) (inLo inHi : Fin inD → ℚ) (L : List Int) (gid0 : ℕ)
      (xv : Fin inD → ℚ) (a : Valuation),
      (∀ i, inLo i ≤ xv i ∧ xv i ≤ inHi i) →
      net.Agree inBase xv a →
      net.consistent gid0 xv L →
      (∀ r ∈ net.encRows inBase inLo inHi L gid0, Le.sat r a)
      ∧ (∀ k, a (net.outBase inBase + k.val) = net.eval xv k) := by
  induction net with
  | last W b =>
      intro inBase inLo inHi L gid0 xv a _hb hag _hcon
      refine ⟨?_, ?_⟩
      · intro r hr
        simp only [MLP.encRows, List.mem_flatMap, List.mem_finRange, true_and] at hr
        obtain ⟨k, hr⟩ := hr
        refine affEqRows_sat _ _ _ _ a ?_ r hr
        rw [hag.lastOut k]
        simp only [preAct]
        have hs : (∑ j, W k j * a (inBase + j.val)) = (∑ j, W k j * xv j) :=
          Finset.sum_congr rfl (fun j _ => by rw [hag.input j])
        rw [hs]
      · intro k
        simp only [MLP.outBase, MLP.eval]
        exact hag.lastOut k
  | @cons inD hidD outD W b rest ih =>
      intro inBase inLo inHi L gid0 xv a hb hag hcon
      simp only [MLP.consistent] at hcon
      have hpb : ∀ i : Fin hidD,
          lbAff W b inLo inHi i ≤ preAct W b xv i ∧ preAct W b xv i ≤ ubAff W b inLo inHi i :=
        fun i => affine_interval_sound (W i) xv inLo inHi (b i)
          (fun j => (hb j).1) (fun j => (hb j).2)
      have hb' : ∀ i : Fin hidD,
          max (lbAff W b inLo inHi i) 0 ≤ postAct W b xv i ∧
          postAct W b xv i ≤ max (ubAff W b inLo inHi i) 0 := by
        refine fun i => ⟨?_, ?_⟩
        · simp only [postAct]; exact max_le_max (hpb i).1 le_rfl
        · simp only [postAct]; exact max_le_max (hpb i).2 le_rfl
      obtain ⟨ih_rows, ih_out⟩ := ih (inBase + inD + hidD + hidD)
        (fun i => max (lbAff W b inLo inHi i) 0) (fun i => max (ubAff W b inLo inHi i) 0)
        L (gid0 + hidD) (postAct W b xv) a hb' hag.rest hcon.2
      refine ⟨?_, ?_⟩
      · intro r hr
        simp only [MLP.encRows, List.mem_append, List.mem_flatMap, List.mem_finRange,
          true_and] at hr
        rcases hr with (((⟨i, hr⟩ | ⟨i, hr⟩) | ⟨i, hr⟩) | hr)
        · -- pre-activation affine equalities
          refine affEqRows_sat _ _ _ _ a ?_ r hr
          rw [hag.consPre i]
          simp only [preAct]
          have hs : (∑ j, W i j * a (inBase + j.val)) = (∑ j, W i j * xv j) :=
            Finset.sum_congr rfl (fun j _ => by rw [hag.input j])
          rw [hs]
        · -- big-M ReLU rows
          refine reluRows_sat (lbAff W b inLo inHi i) (ubAff W b inLo inHi i)
            (inBase + inD + i.val) (inBase + inD + hidD + hidD + i.val)
            (inBase + inD + hidD + i.val) a ?_ ?_ ?_ ?_ r hr
          · rw [hag.consPre i]; exact (hpb i).1
          · rw [hag.consPre i]; exact (hpb i).2
          · rw [hag.consPost i, hag.consPre i]; simp only [postAct]
          · rw [hag.consBin i, hag.consPre i]; simp only [binAct]
        · -- leaf sign rows
          refine leafRows_sat L (gid0 + i.val + 1) (inBase + inD + i.val) a ?_ ?_ r hr
          · intro hmem; rw [hag.consPre i]; exact (hcon.1 i).1 hmem
          · intro hmem; rw [hag.consPre i]; exact (hcon.1 i).2 hmem
        · -- recursive rows
          exact ih_rows r hr
      · intro k
        simp only [MLP.outBase, MLP.eval]
        exact ih_out k

/-! ## Top-level over-approximation and refutation for a general MLP -/

/-- Objective form evaluated at any valuation: `Σ_k c_k · a(out_k)`. -/
lemma MLP.objRow_eval {inD outD : ℕ} (net : MLP inD outD) (inBase : ℕ) (cc : Fin outD → ℚ)
    (rhs : ℚ) (a : Valuation) :
    (net.objRow inBase cc rhs).form.eval a
      = ∑ k, cc k * a (net.outBase inBase + k.val) := by
  simp only [MLP.objRow, LinForm.eval, List.map_ofFn, List.sum_ofFn, Function.comp]

open AptpCheck.Pipeline in
/-- The real trace satisfies the input box rows. -/
lemma MLP.boxRows_sat_trace {inD outD : ℕ} (net : MLP inD outD) (lo hi x : Fin inD → ℚ)
    (hx : ∀ j, lo j ≤ x j ∧ x j ≤ hi j) :
    ∀ r ∈ boxRows lo hi, Le.sat r (net.trace x) := by
  have htx : ∀ j : Fin inD, net.trace x j.val = x j := by
    intro j; have := (net.agree_trace x).input j; rwa [Nat.zero_add] at this
  intro r hr
  simp only [boxRows, List.mem_append, List.mem_ofFn] at hr
  rcases hr with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · simp only [Le.sat, LinForm.eval, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, one_mul, add_zero, htx]
    exact (hx j).2
  · simp only [Le.sat, LinForm.eval, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, neg_one_mul, add_zero, htx]
    linarith [(hx j).1]

open AptpCheck.Pipeline in
/-- **Encoding over-approximation for a general MLP.** For any input `x` in the box whose
true ReLU signs are consistent with the leaf `L`, the real trace valuation is a feasible
point of every emitted row (box + affine equalities + big-M ReLU + leaf signs) and the
objective evaluates to `c · net(x)`. -/
theorem encoding_overapprox_mlp {inD outD : ℕ} (net : MLP inD outD)
    (cc : Fin outD → ℚ) (rhs : ℚ) (lo hi : Fin inD → ℚ) (L : List Int)
    (x : Fin inD → ℚ) (hx : ∀ j, lo j ≤ x j ∧ x j ≤ hi j)
    (hcon : net.consistent 0 x L) :
    ∃ a : Valuation,
      (∀ r ∈ boxRows lo hi ++ net.encRows 0 lo hi L 0, Le.sat r a) ∧
      (net.objRow 0 cc rhs).form.eval a = ∑ k, cc k * net.eval x k := by
  obtain ⟨hrows, hout⟩ :=
    net.encRows_sat_and_out 0 lo hi L 0 x (net.trace x) hx (net.agree_trace x) hcon
  refine ⟨net.trace x, ?_, ?_⟩
  · intro r hr
    rcases List.mem_append.mp hr with hbox | henc
    · exact net.boxRows_sat_trace lo hi x hx r hbox
    · exact hrows r henc
  · rw [net.objRow_eval 0 cc rhs (net.trace x)]
    exact Finset.sum_congr rfl (fun k _ => by rw [hout k])

open AptpCheck.Pipeline in
/-- **Per-leaf refutation for a general MLP.** A Farkas certificate refuting the emitted
rows together with the negated objective proves `c · net(x) > rhs` for every `x` in the
box consistent with the leaf. -/
theorem certified_sound_mlp {inD outD : ℕ} (net : MLP inD outD)
    (cc : Fin outD → ℚ) (rhs : ℚ) (lo hi : Fin inD → ℚ) (L : List Int)
    (x : Fin inD → ℚ) (hx : ∀ j, lo j ≤ x j ∧ x j ≤ hi j)
    (hcon : net.consistent 0 x L)
    (comb : List (ℚ × Le))
    (hsub : ∀ p ∈ comb,
      p.2 ∈ (net.objRow 0 cc rhs :: (boxRows lo hi ++ net.encRows 0 lo hi L 0)))
    (hnn : ∀ p ∈ comb, 0 ≤ p.1)
    (hcancel : (comb.map (fun p => p.1 * p.2.form.eval (net.trace x))).sum = 0)
    (hneg : (comb.map (fun p => p.1 * p.2.rhs)).sum < 0) :
    rhs < ∑ k, cc k * net.eval x k := by
  obtain ⟨hrows, hout⟩ :=
    net.encRows_sat_and_out 0 lo hi L 0 x (net.trace x) hx (net.agree_trace x) hcon
  have hall : ∀ r ∈ boxRows lo hi ++ net.encRows 0 lo hi L 0, Le.sat r (net.trace x) := by
    intro r hr
    rcases List.mem_append.mp hr with h | h
    · exact net.boxRows_sat_trace lo hi x hx r h
    · exact hrows r h
  have h := refute_of_cert (boxRows lo hi ++ net.encRows 0 lo hi L 0) (net.objRow 0 cc rhs)
    (net.trace x) comb hsub hnn hcancel hneg hall
  rw [net.objRow_eval 0 cc rhs (net.trace x)] at h
  rw [show (∑ k, cc k * (net.trace x) (net.outBase 0 + k.val)) = ∑ k, cc k * net.eval x k from
    Finset.sum_congr rfl (fun k _ => by rw [hout k])] at h
  exact h

/-! ## Bridge to the coverage `satLeaf` interface

`consistent` is derived from the coverage-level hypothesis `satLeaf L σ = true` (the leaf
is satisfied by the true sign vector `σ`) together with `signMatch`, which states that `σ`
really is the network's neuron-sign vector at `x`. This lets `certified_sound_mlp` slot
into `Pipeline.certified_sound_abstract`. -/

/-- `σ` gives the correct ReLU sign for every neuron of the sub-network (1-based ids
offset by `gid0`). -/
def MLP.signMatch : {inD outD : ℕ} → MLP inD outD → ℕ → (Fin inD → ℚ) → (Nat → Bool) → Prop
  | _, _, .last _ _, _, _, _ => True
  | _, _, .cons (hidD := hidD) W b rest, gid0, xv, σ =>
      (∀ i : Fin hidD, σ (gid0 + i.val + 1) = decide (0 ≤ preAct W b xv i))
      ∧ rest.signMatch (gid0 + hidD) (postAct W b xv) σ

/-- If `σ` is the true sign vector (`signMatch`) and the leaf is satisfied by `σ`
(`satLeaf`), then the network is consistent with the leaf. -/
lemma MLP.consistent_of_signMatch {inD outD : ℕ} (net : MLP inD outD) :
    ∀ (gid0 : ℕ) (xv : Fin inD → ℚ) (σ : Nat → Bool) (L : List Int),
      net.signMatch gid0 xv σ → satLeaf L σ = true → net.consistent gid0 xv L := by
  induction net with
  | last W b => intro gid0 xv σ L _ _; simp only [MLP.consistent]
  | @cons inD hidD outD W b rest ih =>
      intro gid0 xv σ L hmatch hsat
      simp only [MLP.signMatch] at hmatch
      simp only [MLP.consistent]
      have hsat' : ∀ ℓ ∈ L, (if 0 < ℓ then σ ℓ.natAbs else !σ ℓ.natAbs) = true := by
        simpa only [satLeaf, List.all_eq_true] using hsat
      refine ⟨fun i => ⟨fun hmem => ?_, fun hmem => ?_⟩, ?_⟩
      · have h := hsat' _ hmem
        rw [if_pos (by positivity), Int.natAbs_natCast, hmatch.1 i] at h
        exact of_decide_eq_true h
      · have h := hsat' _ hmem
        rw [if_neg (by omega), Int.natAbs_neg, Int.natAbs_natCast, hmatch.1 i] at h
        simp only [Bool.not_eq_true'] at h
        exact le_of_lt (not_le.mp (of_decide_eq_false h))
      · exact ih (gid0 + hidD) (postAct W b xv) σ L hmatch.2 hsat

open AptpCheck.Pipeline in
/-- **Per-leaf refutation, `satLeaf` form.** As `certified_sound_mlp`, but with the
consistency hypothesis phrased through the coverage `satLeaf` interface: `σ` is the true
sign vector (`signMatch`) and the leaf is satisfied by `σ`. -/
theorem certified_sound_mlp_satLeaf {inD outD : ℕ} (net : MLP inD outD)
    (cc : Fin outD → ℚ) (rhs : ℚ) (lo hi : Fin inD → ℚ) (L : List Int) (σ : Nat → Bool)
    (x : Fin inD → ℚ) (hx : ∀ j, lo j ≤ x j ∧ x j ≤ hi j)
    (hmatch : net.signMatch 0 x σ) (hsat : satLeaf L σ = true)
    (comb : List (ℚ × Le))
    (hsub : ∀ p ∈ comb,
      p.2 ∈ (net.objRow 0 cc rhs :: (boxRows lo hi ++ net.encRows 0 lo hi L 0)))
    (hnn : ∀ p ∈ comb, 0 ≤ p.1)
    (hcancel : (comb.map (fun p => p.1 * p.2.form.eval (net.trace x))).sum = 0)
    (hneg : (comb.map (fun p => p.1 * p.2.rhs)).sum < 0) :
    rhs < ∑ k, cc k * net.eval x k :=
  certified_sound_mlp net cc rhs lo hi L x hx
    (net.consistent_of_signMatch 0 x σ L hmatch hsat) comb hsub hnn hcancel hneg

end AptpCheck.Model
