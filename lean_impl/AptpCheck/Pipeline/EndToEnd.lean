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

/-- Order-insensitive row equality: same sense, same right-hand side, and forms equal *as
functions* (`formEq`, so term reordering / duplicate merging by the solver is fine). -/
def sameSLe (r t : SLe) : Bool :=
  (r.sense == t.sense) && formEq r.form t.form && decide (r.rhs = t.rhs)

theorem sameSLe_sat {r t : SLe} (h : sameSLe r t = true) {a : Valuation}
    (ht : SLe.sat t a) : SLe.sat r a := by
  simp only [sameSLe, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨hsense, hform⟩, hrhs⟩ := h
  have hfe : r.form.eval a = t.form.eval a := formEq_sound hform a
  simp only [SLe.sat] at ht ⊢
  rw [hsense, hfe, hrhs]; exact ht

def leafCheck {inD outD : ℕ} (net : MLP inD outD) (cc : Fin outD → ℚ) (rhs : ℚ)
    (lo hi : Fin inD → ℚ) (L : List Int) (cert : Vipr) : Bool :=
  checkSem cert
  && (conSLes cert).all (fun r => (trustedSLe net cc rhs lo hi L).any (fun t => sameSLe r t))
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
  · -- every CON row semantically matches some trusted row, hence is satisfied by the trace
    obtain ⟨t, htmem, hmatch⟩ := List.any_eq_true.mp ((List.all_eq_true.mp hcon_all) r hr)
    refine sameSLe_sat hmatch ?_
    simp only [trustedSLe] at htmem
    rcases List.mem_append.mp htmem with hmap | hflat
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

/-! ## Assembly via coverage -/

/-- **Whole-network certification.** Pair each leaf with its certificate (via `zip`),
require the paired leaves to cover the activation cube, and check every pair with
`leafCheck`. A length mismatch is handled conservatively: `zip` truncates to the shorter
list, so coverage is demanded of exactly the leaves that actually received a certificate. -/
def certifyMLP {inD outD : ℕ} (net : MLP inD outD) (cc : Fin outD → ℚ) (rhs : ℚ)
    (lo hi : Fin inD → ℚ) (leaves : List (List Int)) (certs : List Vipr) : Bool :=
  checkCoverage ((leaves.zip certs).map Prod.fst)
  && (leaves.zip certs).all (fun p => leafCheck net cc rhs lo hi p.1 p.2)

/-- **Soundness of whole-network certification (proof-side `MLP`).** If `certifyMLP`
accepts, the property `c · net(x) > rhs` holds for every `x` in the input box. -/
theorem certifyMLP_sound {inD outD : ℕ} (net : MLP inD outD) (cc : Fin outD → ℚ) (rhs : ℚ)
    (lo hi : Fin inD → ℚ) (leaves : List (List Int)) (certs : List Vipr)
    (h : certifyMLP net cc rhs lo hi leaves certs = true) :
    ∀ x, (∀ j, lo j ≤ x j ∧ x j ≤ hi j) → rhs < ∑ k, cc k * net.eval x k := by
  simp only [certifyMLP, Bool.and_eq_true] at h
  obtain ⟨hcover, hall⟩ := h
  intro x hx
  refine certified_sound_abstract (Input := Fin inD → ℚ)
    ((leaves.zip certs).map Prod.fst)
    (fun z => ∀ j, lo j ≤ z j ∧ z j ≤ hi j)
    (fun z => rhs < ∑ k, cc k * net.eval z k)
    (fun z => net.trueSign z 0) hcover ?_ hx
  -- refute obligation: each covered leaf has a checked certificate
  intro leaf hleafmem y hymem hsat
  obtain ⟨p, hp, hpfst⟩ := List.mem_map.mp hleafmem
  have hlc : leafCheck net cc rhs lo hi p.1 p.2 = true := (List.all_eq_true.mp hall) p hp
  have hcon : net.consistent 0 y p.1 :=
    net.consistent_of_signMatch 0 y (net.trueSign y 0) p.1 (net.signMatch_trueSign y 0)
      (by rw [hpfst]; exact hsat)
  exact leafCheck_sound net cc rhs lo hi p.1 p.2 hlc y hymem hcon

/-- **End-to-end soundness for a runnable `Network`.** If the network parses to the MLP
normal form `r` and `certifyMLP` accepts, the property holds for the executable
`Network.eval` on every input array whose entries lie in the box. -/
theorem certify_network_sound (net : Network) (r : Σ outD : ℕ, MLP net.inDim outD)
    (hconv : toMLP net = some r) (cc : Fin r.1 → ℚ) (rhs : ℚ)
    (lo hi : Fin net.inDim → ℚ) (leaves : List (List Int)) (certs : List Vipr)
    (x : Array ℚ)
    (hx : ∀ j : Fin net.inDim, lo j ≤ x.getD j.val 0 ∧ x.getD j.val 0 ≤ hi j)
    (h : certifyMLP r.2 cc rhs lo hi leaves certs = true) :
    rhs < ∑ k : Fin r.1, cc k * (Network.eval net x).getD k.val 0 := by
  have hsound := certifyMLP_sound r.2 cc rhs lo hi leaves certs h
    (fun j => x.getD j.val 0) hx
  rw [show (∑ k : Fin r.1, cc k * (Network.eval net x).getD k.val 0)
        = ∑ k : Fin r.1, cc k * r.2.eval (fun j => x.getD j.val 0) k from
      Finset.sum_congr rfl (fun k _ => by rw [toMLP_eval net r hconv x k])]
  exact hsound

/-- SCIP numbers certificate variables in its own order; each cert index `i` carries a
name ending in our encoder's variable id (we emit `V{k}`; SCIP may prefix it, e.g.
`t_V{k}`). Recover `k` from the trailing digits of the name. -/
def ourIdxOfName (s : String) : Nat :=
  (Ast.natOfDigits? (s.toList.reverse.takeWhile Char.isDigit).reverse).getD 0

/-- Relabel a certificate's variable indices from SCIP's index space back into the
encoder's, using the `VAR` names. Untrusted (a wrong relabel only makes the correspondence
check fail); `checkSem` is invariant under consistent variable renaming, so a valid
certificate stays valid. -/
def relabelVipr (v : Ast.Vipr) : Ast.Vipr :=
  let m : Nat → Nat := fun i => ourIdxOfName (v.varNames.getD i "")
  let rf : LinForm → LinForm := fun f => f.map (fun t => ⟨m t.idx, t.coeff⟩)
  { v with
    cons := v.cons.map (fun c => { c with form := rf c.form })
    ders := v.ders.map (fun d => { d with form := rf d.form })
    objTerms := v.objTerms.map (fun p => (m p.1, p.2))
    intVars := v.intVars.map m }

/-- Executable per-leaf check for a parsed `Network` (the CLI's hook into `leafCheck`):
converts the network to its MLP with the SAME box→(lo,hi) and objective conventions the
encoder uses, then runs the full `leafCheck` (verified checker + certificate↔encoding
correspondence + integer-variable check). `false` if the network is not an MLP. When this
returns `true` for every leaf and coverage holds, `certify_network_sound` applies. -/
def leafCheckNet (net : Network) (box : Array (ℚ × ℚ)) (leaf : List Int)
    (c : Array ℚ) (rhs : ℚ) (cert : Ast.Vipr) : Bool :=
  match toMLP net with
  | none => false
  | some ⟨_outD, mlp⟩ =>
      leafCheck mlp (fun k => c.getD k.val 0) rhs
        (fun i => (box.getD i.val (0, 0)).1) (fun i => (box.getD i.val (0, 0)).2) leaf
        (relabelVipr cert)

end AptpCheck.Pipeline
