import AptpCheck.Ast.Vipr
import AptpCheck.Cert.Vipr

/-!
# VIPR certificate → infeasibility (verified endpoint)

Connects the (verified) VIPR parser `Ast/Vipr` to the (verified) proof-by-cases
checker `Cert/Vipr`. Given a parsed certificate `v`, its `CON` rows are `v.conLes`
and its integer-declared variables are `v.intVars`. If `checkRefTree` validates a
refutation tree `t` against `v.conLes`, then that constraint system is infeasible.

The refutation tree `t` is supplied by an *untrusted* producer (a small VIPR-flat →
tree converter, or SCIP's search post-processed); it need not be trusted, because
`checkRefTree` re-validates it against `v.conLes` — an invalid tree is rejected, and a
valid one is, by `checkRefTree_sound`, a genuine refutation. So this endpoint keeps the
trusted base to the kernel, the (verified) parser, and the (verified) checker.
-/

namespace AptpCheck.Pipeline

open AptpCheck.Cert

/-- Integer-variable predicate read off a certificate's `INT` section. -/
def viprIsInt (v : Ast.Vipr) : Nat → Bool := fun j => decide (j ∈ v.intVars)

/-- **VIPR certificate ⟹ infeasibility.** If `checkRefTree` validates a refutation
tree against the certificate's `CON` rows, then no valuation whose integer-declared
variables are integral satisfies those rows. Composes `checkRefTree_sound` with the
parser's `conLes`. -/
theorem vipr_infeasible (v : Ast.Vipr) (t : RefTree)
    (h : checkRefTree (viprIsInt v) v.conLes t = true) :
    ∀ a, (∀ j ∈ v.intVars, IsIntVal (a j)) → (∀ c ∈ v.conLes, Le.sat c a) → False := by
  intro a hint hrows
  refine checkRefTree_sound (viprIsInt v) v.conLes t h a ?_ hrows
  intro j hj
  exact hint j (by simpa [viprIsInt] using hj)

end AptpCheck.Pipeline
