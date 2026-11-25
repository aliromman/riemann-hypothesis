module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv
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

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace CrystallineSemistableComparison.Om

section
variable {K : Type} [Field K] {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

abbrev HodgeC (a j : ℕ) : Type := GlobalTheory.HodgeCoh.hodgeH q a j


variable {q} in
def pullC {p : Y ⟶ Spec (CommRingCat.of K)} (u : Y ⟶ X) (hu : u ≫ q = p) (a j : ℕ) : HodgeC q a j →ₗ[K] HodgeC p a j :=
  GlobalTheory.HodgeCoh.hodgePull hu a j

end

end CrystallineSemistableComparison.Om
