import AptpCheck.Model.EncodeFold
import AptpCheck.Model.TrueSign
import AptpCheck.Model.NetworkMLP
import AptpCheck.Cert.ViprSem
import AptpCheck.Pipeline.ViprFlatCheck
import AptpCheck.Pipeline.Compose
import AptpCheck.Pipeline.Affine

/-!
# End-to-end soundness capstone

This module ties the already-proven pieces together into the paper's top-level theorem:
*coverage holds + every leaf's certificate checks ⟹ the network satisfies the property.*

The glue is a **certificate ↔ encoding correspondence** check, `leafCheck`: a VIPR
certificate `cert` certifies a leaf's region iff (a) `checkSem cert` accepts it, (b) every
CON row of `cert` is (syntactically) one of the *trusted* rows the verified encoder
`encFold` would emit for this leaf (`trustedSLe`), and (c) every integer variable `cert`
declares really is one of the encoder's binary ids. Under those three facts the real trace
`net.trace x` satisfies all of `cert`'s CON rows and is integral on its integer variables,
so `checkSem_sound` refutes any counterexample — giving per-leaf refutation
(`leafCheck_sound`). `certifyMLP`/`certifyMLP_sound` then compose this with coverage
(`certified_sound_abstract`, `signMatch_trueSign`, `consistent_of_signMatch`), and
`certify_network_sound` transports the result through `toMLP_eval` to a runnable `Network`.

Everything is kernel-checked and axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

namespace AptpCheck.Pipeline

open AptpCheck.Model AptpCheck.Cert AptpCheck.Coverage AptpCheck.Ast

/-! ## Certificate ↔ encoding correspondence -/

/-- View a `≤`-row as a sensed constraint (sense `'L'`). -/
def toSLeL (l : Le) : SLe := ⟨'L', l.form, l.rhs⟩

/-- `toSLeL` preserves satisfaction (both reduce to `l.form.eval a ≤ l.rhs`). -/
lemma toSLeL_sat (l : Le) (a : Valuation) : SLe.sat (toSLeL l) a ↔ Le.sat l a := by
  unfold toSLeL SLe.sat Le.sat
  simp

/-- The **trusted sensed rows** for a leaf: the encoder's box rows, `encFold` rows and
objective row (as `'L'` rows), plus a `0 ≤ b ≤ 1` bound pair for each encoder binary id.
A certificate is trusted only if every one of its CON rows is a member of this list. -/
def trustedSLe {inD outD : ℕ} (net : MLP inD outD) (cc : Fin outD → ℚ) (rhs : ℚ)
    (lo hi : Fin inD → ℚ) (L : List Int) : List SLe :=
  (boxRows lo hi ++ net.encFold 0 lo hi L 0 ++ [net.objRow 0 cc rhs]).map toSLeL
  ++ (net.encFoldBinIds 0 lo hi L 0).flatMap
      (fun b => [(⟨'G', [⟨b, 1⟩], 0⟩ : SLe), ⟨'L', [⟨b, 1⟩], 1⟩])

/-- The leaf-certificate correspondence check. -/
def leafCheck {inD outD : ℕ} (net : MLP inD outD) (cc : Fin outD → ℚ) (rhs : ℚ)
    (lo hi : Fin inD → ℚ) (L : List Int) (cert : Vipr) : Bool :=
  checkSem cert
  && (conSLes cert).all (fun r => decide (r ∈ trustedSLe net cc rhs lo hi L))
  && cert.intVars.all (fun j => decide (j ∈ net.encFoldBinIds 0 lo hi L 0))

/-! ## The binary trace values lie in `{0,1}` -/

/-- **Core induction (binary `[0,1]` bounds).** Every encoder binary id holds a value in
`[0,1]` in an agreeing valuation (indeed it is a `binAct`, i.e. `0` or `1`). -/
lemma binVal_zeroOne_core {inD outD : ℕ} (net : MLP inD outD) :
    ∀ (inBase : ℕ) (inLo inHi : Fin inD → ℚ) (L : List Int) (gid0 : ℕ)
      (xv : Fin inD → ℚ) (a : Valuation),
      net.Agree inBase xv a →
      ∀ id ∈ net.encFoldBinIds inBase inLo inHi L gid0, 0 ≤ a id ∧ a id ≤ 1 := by
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
            · rw [if_pos hp]; constructor <;> norm_num
            · rw [if_neg hp]; constructor <;> norm_num
      · exact ih (inBase + inD + hidD + hidD)
          (fun i => max (lbAff W b inLo inHi i) 0) (fun i => max (ubAff W b inLo inHi i) 0)
          L (gid0 + hidD) (postAct W b xv) a hag.rest id hid

/-- Every encoder binary id holds a value in `[0,1]` in the real trace. -/
lemma binVal_zeroOne {inD outD : ℕ} (net : MLP inD outD)
    (lo hi : Fin inD → ℚ) (L : List Int) (x : Fin inD → ℚ) :
    ∀ id ∈ net.encFoldBinIds 0 lo hi L 0, 0 ≤ net.trace x id ∧ net.trace x id ≤ 1 :=
  binVal_zeroOne_core net 0 lo hi L 0 x (net.trace x) (net.agree_trace x)

/-! ## Per-leaf soundness -/

/-- **Per-leaf refutation via a checked certificate.** If `leafCheck` accepts `cert` for a
leaf `L`, then on every input `x` in the box whose signs are consistent with `L`, the
network's objective strictly exceeds `rhs`. -/
theorem leafCheck_sound {inD outD : ℕ} (net : MLP inD outD) (cc : Fin outD → ℚ) (rhs : ℚ)
    (lo hi : Fin inD → ℚ) (L : List Int) (cert : Vipr)
    (h : leafCheck net cc rhs lo hi L cert = true) :
    ∀ x, (∀ j, lo j ≤ x j ∧ x j ≤ hi j) → net.consistent 0 x L →
      rhs < ∑ k, cc k * net.eval x k := by
  intro x hx hcon
  by_contra hle
  rw [not_lt] at hle
  -- extract the three checked facts
  simp only [leafCheck, Bool.and_eq_true] at h
  obtain ⟨⟨hsem, hcon_all⟩, hint_all⟩ := h
  -- the real trace satisfies all encoder rows and holds the true output
  obtain ⟨hrows, hout⟩ :=
    net.encFold_sat_and_out 0 lo hi L 0 x (net.trace x) hx (net.agree_trace x) hcon
  -- refute via the certificate checker at the real trace
  refine checkSem_sound cert hsem (net.trace x) (fun j hj => ?_) (fun r hr => ?_)
  · -- integrality: every declared integer var is an encoder binary id
    exact encFold_binIds_int net lo hi L x j
      (of_decide_eq_true ((List.all_eq_true.mp hint_all) j hj))
  · -- every CON row is a trusted row, hence satisfied by the trace
    have hrt : r ∈ trustedSLe net cc rhs lo hi L :=
      of_decide_eq_true ((List.all_eq_true.mp hcon_all) r hr)
    simp only [trustedSLe] at hrt
    rcases List.mem_append.mp hrt with hmap | hflat
    · -- r = toSLeL l for l a box/encFold/objective row
      obtain ⟨l, hlmem, rfl⟩ := List.mem_map.mp hmap
      rw [toSLeL_sat]
      rcases List.mem_append.mp hlmem with hl | hlobj
      · rcases List.mem_append.mp hl with hbox | henc
        · exact net.boxRows_sat_trace lo hi x hx l hbox
        · exact hrows l henc
      · rw [List.mem_singleton] at hlobj; subst hlobj
        have he : (net.objRow 0 cc rhs).form.eval (net.trace x) = ∑ k, cc k * net.eval x k := by
          rw [net.objRow_eval 0 cc rhs (net.trace x)]
          exact Finset.sum_congr rfl (fun k _ => by rw [hout k])
        show (net.objRow 0 cc rhs).form.eval (net.trace x) ≤ (net.objRow 0 cc rhs).rhs
        rw [he]; exact hle
    · -- r is a binary `[0,1]` bound for some encoder binary id
      obtain ⟨bid, hbid, hr2⟩ := List.mem_flatMap.mp hflat
      obtain ⟨hb0, hb1⟩ := binVal_zeroOne net lo hi L x bid hbid
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr2
      rcases hr2 with rfl | rfl
      · show (0 : ℚ) ≤ LinForm.eval [⟨bid, 1⟩] (net.trace x)
        simpa [LinForm.eval] using hb0
      · show LinForm.eval [⟨bid, 1⟩] (net.trace x) ≤ (1 : ℚ)
        simpa [LinForm.eval] using hb1

end AptpCheck.Pipeline
