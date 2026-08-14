import Mathlib
import AptpCheck.Model.Network
import AptpCheck.Model.Encoding
import AptpCheck.Cert.LinCon
import AptpCheck.Cert.Vipr
import AptpCheck.Coverage.Tautology
import AptpCheck.Pipeline.Affine
import AptpCheck.Model.EncodingSound

/-!
# Leaf-aware MILP encoder (`encFold`) and its over-approximation soundness

`Model/EncodingSound` gives a **uniform** verified encoder `MLP.encRows`: it emits the
full big-M ReLU gadget (a `0/1` binary plus four inequalities) for *every* hidden
neuron, even ones the interval bounds or the leaf `L` already sign-fix. That wastes an
integer variable per stable neuron.

This module builds `MLP.encFold`, which keeps the **exact same fixed positional variable
layout as `encRows`** (input ids, then per hidden layer: pre-activation, binary,
post-activation ids at the same offsets) so the *entire* verified trace machinery of
`EncodingSound` — `MLP.trace`, `preAct`/`postAct`/`binAct`, `MLP.traceList`, the
`traceList_cons_*` lemmas, `MLP.Agree`, `agree_trace`, `MLP.outBase`, `MLP.objRow`,
`MLP.consistent`, `lbAff`/`ubAff` — is reused verbatim. The *only* change vs `encRows` is
**which rows are emitted per neuron**, decided from `L` and the interval `[lbAff,ubAff]`:

* **active** (`0 ≤ lbAff` stable-active, *or* `L` fixes it active): emit `post = pre`
  (two `≤` rows) plus the sign row `pre ≥ 0` if fixed active. No binary rows.
* **inactive** (`ubAff ≤ 0`, *or* `L` fixes it inactive): emit `post = 0` (two `≤` rows)
  plus `pre ≤ 0` if fixed inactive. No binary rows.
* **unstable** (otherwise): emit the SAME `reluRows lbAff ubAff pre post bin` big-M gadget
  `encRows` uses, referencing the binary slot.

The binary slot still exists positionally (layout unchanged), but rows reference it ONLY
in the unstable case — so sign-fixed neurons contribute no integer variable to the MILP.
`MLP.encFoldBinIds` lists exactly the unstable neurons' binary ids.

Everything is kernel-checked and axiom-clean (`[propext, Classical.choice, Quot.sound]`).
The over-approximation and per-leaf refutation theorems (`encFold_overapprox`,
`certified_sound_mlp_fold`) mirror `encoding_overapprox_mlp` / `certified_sound_mlp`.
-/

namespace AptpCheck.Model

open AptpCheck.Cert AptpCheck.Coverage

/-! ## Per-neuron fold rows -/

/-- The MILP rows emitted for a single hidden neuron with interval `[lb,ub]`, leaf `L`,
1-based global id `gid`, and the positional variables `preId`/`postId`/`binId`.

* active (`0 ≤ lb` or `gid ∈ L`): `post = pre` (two rows) `+` `pre ≥ 0` if fixed active;
* inactive (`ub ≤ 0` or `-gid ∈ L`): `post = 0` (two rows) `+` `pre ≤ 0` if fixed inactive;
* unstable: the four big-M `reluRows`.

The binary id `binId` is referenced only in the unstable branch. -/
def foldNeuronRows (lb ub : ℚ) (L : List Int) (gid preId postId binId : Nat) : List Le :=
  if 0 ≤ lb ∨ (↑gid : Int) ∈ L then
    (⟨[⟨postId, 1⟩, ⟨preId, -1⟩], 0⟩ : Le) ::
    (⟨[⟨preId, 1⟩, ⟨postId, -1⟩], 0⟩ : Le) ::
    (if (↑gid : Int) ∈ L then [(⟨[⟨preId, -1⟩], 0⟩ : Le)] else [])
  else if ub ≤ 0 ∨ (-(↑gid) : Int) ∈ L then
    (⟨[⟨postId, 1⟩], 0⟩ : Le) ::
    (⟨[⟨postId, -1⟩], 0⟩ : Le) ::
    (if (-(↑gid) : Int) ∈ L then [(⟨[⟨preId, 1⟩], 0⟩ : Le)] else [])
  else
    reluRows lb ub preId postId binId

/-- The real activation trace satisfies every fold row for one neuron, under the same
hypotheses as `reluRows_sat` plus the leaf-consistency facts (which the caller supplies
from `MLP.consistent`). -/
lemma foldNeuronRows_sat (lb ub : ℚ) (L : List Int) (gid preId postId binId : Nat)
    (a : Valuation)
    (hlb : lb ≤ a preId) (hub : a preId ≤ ub)
    (hpost : a postId = max (a preId) 0)
    (hbin : a binId = if 0 ≤ a preId then (1 : ℚ) else 0)
    (hact : (↑gid : Int) ∈ L → 0 ≤ a preId)
    (hinact : (-(↑gid) : Int) ∈ L → a preId ≤ 0) :
    ∀ r ∈ foldNeuronRows lb ub L gid preId postId binId, Le.sat r a := by
  unfold foldNeuronRows
  by_cases hActive : 0 ≤ lb ∨ (↑gid : Int) ∈ L
  · rw [if_pos hActive]
    have hpre : 0 ≤ a preId := by
      rcases hActive with h | h
      · linarith [hlb]
      · exact hact h
    have hpe : a postId = a preId := by rw [hpost, max_eq_left hpre]
    intro r hr
    simp only [List.mem_cons] at hr
    rcases hr with rfl | rfl | hr
    · simp only [Le.sat, LinForm.eval, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil]
      linarith [hpe]
    · simp only [Le.sat, LinForm.eval, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil]
      linarith [hpe]
    · by_cases hc : (↑gid : Int) ∈ L
      · rw [if_pos hc, List.mem_singleton] at hr
        subst hr
        simp only [Le.sat, LinForm.eval, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil]
        linarith [hact hc]
      · rw [if_neg hc] at hr; exact absurd hr (by simp)
  · rw [if_neg hActive]
    by_cases hInactive : ub ≤ 0 ∨ (-(↑gid) : Int) ∈ L
    · rw [if_pos hInactive]
      have hpre : a preId ≤ 0 := by
        rcases hInactive with h | h
        · linarith [hub]
        · exact hinact h
      have hpz : a postId = 0 := by rw [hpost, max_eq_right hpre]
      intro r hr
      simp only [List.mem_cons] at hr
      rcases hr with rfl | rfl | hr
      · simp only [Le.sat, LinForm.eval, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil]
        linarith [hpz]
      · simp only [Le.sat, LinForm.eval, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil]
        linarith [hpz]
      · by_cases hc : (-(↑gid) : Int) ∈ L
        · rw [if_pos hc, List.mem_singleton] at hr
          subst hr
          simp only [Le.sat, LinForm.eval, List.map_cons, List.map_nil, List.sum_cons,
            List.sum_nil]
          linarith [hinact hc]
        · rw [if_neg hc] at hr; exact absurd hr (by simp)
    · rw [if_neg hInactive]
      exact reluRows_sat lb ub preId postId binId a hlb hub hpost hbin

/-! ## The leaf-aware encoder -/

/-- Leaf-aware MILP rows. Same signature and same positional variable layout as
`MLP.encRows`; only the per-neuron row set differs (via `foldNeuronRows`). The pre-
activation affine-equality rows and the terminal-layer affine-equality rows are emitted
identically to `encRows`. -/
def MLP.encFold : {inD outD : ℕ} → MLP inD outD → ℕ → (Fin inD → ℚ) → (Fin inD → ℚ) →
    List Int → ℕ → List Le
  | inD, outD, .last W b, inBase, _inLo, _inHi, _L, _gid0 =>
      (List.finRange outD).flatMap (fun k =>
        affEqRows (inBase + inD + k.val) (fun j => inBase + j.val) (fun j => W k j) (b k))
  | inD, _outD, .cons (hidD := hidD) W b rest, inBase, inLo, inHi, L, gid0 =>
      (List.finRange hidD).flatMap (fun i =>
        affEqRows (inBase + inD + i.val) (fun j => inBase + j.val) (fun j => W i j) (b i))
      ++ (List.finRange hidD).flatMap (fun i =>
        foldNeuronRows (lbAff W b inLo inHi i) (ubAff W b inLo inHi i) L (gid0 + i.val + 1)
          (inBase + inD + i.val) (inBase + inD + hidD + hidD + i.val)
          (inBase + inD + hidD + i.val))
      ++ rest.encFold (inBase + inD + hidD + hidD)
          (fun i => max (lbAff W b inLo inHi i) 0) (fun i => max (ubAff W b inLo inHi i) 0)
          L (gid0 + hidD)

/-- The binary variable ids that `encFold` actually references: exactly the unstable
neurons' binary slots (the sign-fixed / stable neurons contribute none). These are the
only integer variables the reduced MILP needs. -/
def MLP.encFoldBinIds : {inD outD : ℕ} → MLP inD outD → ℕ → (Fin inD → ℚ) → (Fin inD → ℚ) →
    List Int → ℕ → List Nat
  | _, _, .last _ _, _, _, _, _, _ => []
  | inD, _outD, .cons (hidD := hidD) W b rest, inBase, inLo, inHi, L, gid0 =>
      (List.finRange hidD).flatMap (fun i =>
        if 0 ≤ lbAff W b inLo inHi i ∨ (↑(gid0 + i.val + 1) : Int) ∈ L then ([] : List Nat)
        else if ubAff W b inLo inHi i ≤ 0 ∨ (-(↑(gid0 + i.val + 1)) : Int) ∈ L then []
        else [inBase + inD + hidD + i.val])
      ++ rest.encFoldBinIds (inBase + inD + hidD + hidD)
          (fun i => max (lbAff W b inLo inHi i) 0) (fun i => max (ubAff W b inLo inHi i) 0)
          L (gid0 + hidD)

/-! ## The main induction: emitted rows are satisfied and the output block is exact

This mirrors `MLP.encRows_sat_and_out` verbatim; the terminal-layer case and the recursive
routing are identical (the `last` case of `encFold` equals that of `encRows`), and the only
new work is the middle per-neuron flatMap, discharged by `foldNeuronRows_sat` in place of
the `reluRows_sat`/`leafRows_sat` pair. -/

/-- **Core induction (fold encoder).** If the input real values `xv` lie in `[inLo,inHi]`,
the abstract valuation `a` agrees with the trace list from `inBase`, and the leaf is
consistent, then `a` satisfies every fold row and the output block holds the true network
output. -/
lemma MLP.encFold_sat_and_out {inD outD : ℕ} (net : MLP inD outD) :
    ∀ (inBase : ℕ) (inLo inHi : Fin inD → ℚ) (L : List Int) (gid0 : ℕ)
      (xv : Fin inD → ℚ) (a : Valuation),
      (∀ i, inLo i ≤ xv i ∧ xv i ≤ inHi i) →
      net.Agree inBase xv a →
      net.consistent gid0 xv L →
      (∀ r ∈ net.encFold inBase inLo inHi L gid0, Le.sat r a)
      ∧ (∀ k, a (net.outBase inBase + k.val) = net.eval xv k) := by
  induction net with
  | last W b =>
      intro inBase inLo inHi L gid0 xv a _hb hag _hcon
      refine ⟨?_, ?_⟩
      · intro r hr
        simp only [MLP.encFold, List.mem_flatMap, List.mem_finRange, true_and] at hr
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
        simp only [MLP.encFold, List.mem_append, List.mem_flatMap, List.mem_finRange,
          true_and] at hr
        rcases hr with ((⟨i, hr⟩ | ⟨i, hr⟩) | hr)
        · -- pre-activation affine equalities (identical to `encRows`)
          refine affEqRows_sat _ _ _ _ a ?_ r hr
          rw [hag.consPre i]
          simp only [preAct]
          have hs : (∑ j, W i j * a (inBase + j.val)) = (∑ j, W i j * xv j) :=
            Finset.sum_congr rfl (fun j _ => by rw [hag.input j])
          rw [hs]
        · -- per-neuron fold rows (the only new case)
          refine foldNeuronRows_sat (lbAff W b inLo inHi i) (ubAff W b inLo inHi i)
            L (gid0 + i.val + 1) (inBase + inD + i.val)
            (inBase + inD + hidD + hidD + i.val) (inBase + inD + hidD + i.val)
            a ?_ ?_ ?_ ?_ ?_ ?_ r hr
          · rw [hag.consPre i]; exact (hpb i).1
          · rw [hag.consPre i]; exact (hpb i).2
          · rw [hag.consPost i, hag.consPre i]; simp only [postAct]
          · rw [hag.consBin i, hag.consPre i]; simp only [binAct]
          · intro hmem; rw [hag.consPre i]; exact (hcon.1 i).1 hmem
          · intro hmem; rw [hag.consPre i]; exact (hcon.1 i).2 hmem
        · -- recursive rows
          exact ih_rows r hr
      · intro k
        simp only [MLP.outBase, MLP.eval]
        exact ih_out k

/-! ## Top-level over-approximation for the fold encoder -/

open AptpCheck.Pipeline in
/-- **Encoding over-approximation for the leaf-aware encoder.** For any input `x` in the
box whose true ReLU signs are consistent with the leaf `L`, the real trace valuation is a
feasible point of every emitted fold row (box + affine equalities + per-neuron fold rows)
and the objective evaluates to `c · net(x)`. Mirrors `encoding_overapprox_mlp`. -/
theorem encFold_overapprox {inD outD : ℕ} (net : MLP inD outD)
    (cc : Fin outD → ℚ) (rhs : ℚ) (lo hi : Fin inD → ℚ) (L : List Int)
    (x : Fin inD → ℚ) (hx : ∀ j, lo j ≤ x j ∧ x j ≤ hi j)
    (hcon : net.consistent 0 x L) :
    ∃ a : Valuation,
      (∀ r ∈ boxRows lo hi ++ net.encFold 0 lo hi L 0, Le.sat r a) ∧
      (net.objRow 0 cc rhs).form.eval a = ∑ k, cc k * net.eval x k := by
  obtain ⟨hrows, hout⟩ :=
    net.encFold_sat_and_out 0 lo hi L 0 x (net.trace x) hx (net.agree_trace x) hcon
  refine ⟨net.trace x, ?_, ?_⟩
  · intro r hr
    rcases List.mem_append.mp hr with hbox | henc
    · exact net.boxRows_sat_trace lo hi x hx r hbox
    · exact hrows r henc
  · rw [net.objRow_eval 0 cc rhs (net.trace x)]
    exact Finset.sum_congr rfl (fun k _ => by rw [hout k])

/-! ## Integrality of the referenced binary ids

Every id `encFold` references a binary variable for (i.e. every id in `encFoldBinIds`)
carries a genuine `binAct` value in the real trace, which is `0` or `1` — hence integral.
This certifies that the reduced MILP's integer-variable set is sound: those variables
really do take integer values at the real trace. -/

/-- **Core induction (binary integrality).** Under agreement, the abstract valuation is
integer-valued (indeed `∈ {0,1}`) on every id in `encFoldBinIds`. -/
lemma MLP.encFoldBinIds_int_core {inD outD : ℕ} (net : MLP inD outD) :
    ∀ (inBase : ℕ) (inLo inHi : Fin inD → ℚ) (L : List Int) (gid0 : ℕ)
      (xv : Fin inD → ℚ) (a : Valuation),
      net.Agree inBase xv a →
      ∀ id ∈ net.encFoldBinIds inBase inLo inHi L gid0, IsIntVal (a id) := by
  induction net with
  | last W b =>
      intro inBase inLo inHi L gid0 xv a _hag id hid
      simp only [MLP.encFoldBinIds] at hid
      exact absurd hid (by simp)
  | @cons inD hidD outD W b rest ih =>
      intro inBase inLo inHi L gid0 xv a hag id hid
      simp only [MLP.encFoldBinIds, List.mem_append, List.mem_flatMap, List.mem_finRange,
        true_and] at hid
      rcases hid with ⟨i, hid⟩ | hid
      · by_cases h1 : 0 ≤ lbAff W b inLo inHi i ∨ (↑(gid0 + i.val + 1) : Int) ∈ L
        · rw [if_pos h1] at hid; exact absurd hid (by simp)
        · rw [if_neg h1] at hid
          by_cases h2 : ubAff W b inLo inHi i ≤ 0 ∨ (-(↑(gid0 + i.val + 1)) : Int) ∈ L
          · rw [if_pos h2] at hid; exact absurd hid (by simp)
          · rw [if_neg h2, List.mem_singleton] at hid
            subst hid
            rw [hag.consBin i]
            simp only [binAct]
            by_cases hp : 0 ≤ preAct W b xv i
            · rw [if_pos hp]; exact ⟨1, by norm_num⟩
            · rw [if_neg hp]; exact ⟨0, by norm_num⟩
      · exact ih (inBase + inD + hidD + hidD)
          (fun i => max (lbAff W b inLo inHi i) 0) (fun i => max (ubAff W b inLo inHi i) 0)
          L (gid0 + hidD) (postAct W b xv) a hag.rest id hid

/-- **Binary integrality for the real trace.** Every binary id that `encFold` references
holds an integer value in the real trace `net.trace x` (in fact its `binAct`, which is
`0`/`1`). This is the hypothesis the VIPR/MILP integer-variable interface needs. -/
theorem encFold_binIds_int {inD outD : ℕ} (net : MLP inD outD)
    (lo hi : Fin inD → ℚ) (L : List Int) (x : Fin inD → ℚ) :
    ∀ id ∈ net.encFoldBinIds 0 lo hi L 0, IsIntVal (net.trace x id) :=
  net.encFoldBinIds_int_core 0 lo hi L 0 x (net.trace x) (net.agree_trace x)

/-! ## Per-leaf refutation for the fold encoder -/

open AptpCheck.Pipeline in
/-- **Per-leaf refutation for the leaf-aware encoder.** A Farkas certificate refuting the
fold rows together with the negated objective proves `c · net(x) > rhs` for every `x` in
the box consistent with the leaf. Mirrors `certified_sound_mlp`; composes with
`Pipeline.certified_sound_abstract` exactly as the uniform version does (the refutation is
a pure `≤`-row Farkas step, so it needs no integrality — that is supplied separately by
`encFold_binIds_int` for the MILP integer-variable set). -/
theorem certified_sound_mlp_fold {inD outD : ℕ} (net : MLP inD outD)
    (cc : Fin outD → ℚ) (rhs : ℚ) (lo hi : Fin inD → ℚ) (L : List Int)
    (x : Fin inD → ℚ) (hx : ∀ j, lo j ≤ x j ∧ x j ≤ hi j)
    (hcon : net.consistent 0 x L)
    (comb : List (ℚ × Le))
    (hsub : ∀ p ∈ comb,
      p.2 ∈ (net.objRow 0 cc rhs :: (boxRows lo hi ++ net.encFold 0 lo hi L 0)))
    (hnn : ∀ p ∈ comb, 0 ≤ p.1)
    (hcancel : (comb.map (fun p => p.1 * p.2.form.eval (net.trace x))).sum = 0)
    (hneg : (comb.map (fun p => p.1 * p.2.rhs)).sum < 0) :
    rhs < ∑ k, cc k * net.eval x k := by
  obtain ⟨hrows, hout⟩ :=
    net.encFold_sat_and_out 0 lo hi L 0 x (net.trace x) hx (net.agree_trace x) hcon
  have hall : ∀ r ∈ boxRows lo hi ++ net.encFold 0 lo hi L 0, Le.sat r (net.trace x) := by
    intro r hr
    rcases List.mem_append.mp hr with h | h
    · exact net.boxRows_sat_trace lo hi x hx r h
    · exact hrows r h
  have h := refute_of_cert (boxRows lo hi ++ net.encFold 0 lo hi L 0) (net.objRow 0 cc rhs)
    (net.trace x) comb hsub hnn hcancel hneg hall
  rw [net.objRow_eval 0 cc rhs (net.trace x)] at h
  rw [show (∑ k, cc k * (net.trace x) (net.outBase 0 + k.val)) = ∑ k, cc k * net.eval x k from
    Finset.sum_congr rfl (fun k _ => by rw [hout k])] at h
  exact h

end AptpCheck.Model
