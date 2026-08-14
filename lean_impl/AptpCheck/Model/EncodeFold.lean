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

end AptpCheck.Model
