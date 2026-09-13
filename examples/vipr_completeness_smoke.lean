import ViprCheck.Cert.ViprCompleteness

/-! A concrete LP Farkas witness compiled into a closed VIPR certificate. -/

namespace ViprCompletenessSmoke

open ViprCheck.Cert ViprCheck.Cert.ViprSystem ViprCheck.Cert.ViprCompleteness

def lpBase : List SLe :=
  [⟨'L', [⟨0, 1⟩], 0⟩, ⟨'G', [⟨0, 1⟩], 1⟩]

def lpWitness : RationalFarkasWitness lpBase :=
  { comb := [(1, 0), (-1, 1)]
    referencesPast := by decide +kernel
    suitable := by
      intro p hp
      simp [lpBase, resolve, sinitPool, spoolRow, sdflt, senseSignReal] at hp ⊢
      rcases hp with rfl | rfl <;> simp
    zero := by
      intro a
      simp [lpBase, resolve, sinitPool, spoolRow, sdflt, scomb, combine,
        combineForm, SLe.toLe, LinForm.scale, evalReal]
    negative := by
      norm_num [lpBase, resolve, sinitPool, spoolRow, sdflt, scomb, combine, SLe.toLe] }

example : CertificateValid [] lpBase [lpWitness.step] :=
  farkasWitness_to_vipr lpWitness

end ViprCompletenessSmoke
