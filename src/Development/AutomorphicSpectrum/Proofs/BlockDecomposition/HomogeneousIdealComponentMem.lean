module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.Geo

theorem homIdeal_homog {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N) :
    ∀ f ∈ homIdeal i, ∀ n : ℕ, MvPolynomial.homogeneousComponent n f ∈ homIdeal i := by
  intro f hf n
  have hI : (homIdeal i).IsHomogeneous (grK K N) := by
    refine Ideal.homogeneous_span (grK K N) _ ?_
    rintro g ⟨d, hg, -⟩
    exact ⟨d • 1, hg⟩
  have h := hI n hf
  have e : ((DirectSum.decompose (grK K N) f n : grK K N n) : MvPolynomial (Fin (N + 1)) K) =
      MvPolynomial.homogeneousComponent n f :=
    MvPolynomial.decomposition.decompose'_apply f n
  exact e ▸ h

end GlobalTheory.CompanionTheory.Geo
