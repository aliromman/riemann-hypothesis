module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
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

noncomputable section

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.Mum

def Factor.Alg {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} (F : Factor D D') : Prop :=
  (∃ b : ℕ, 0 < b ∧ Star.star F.e * F.e = b • (Star.star F.e * F.f * F.e)) ∧
    Star.star F.e * F.f * F.e = Star.star F.e * Star.star F.f * F.e ∧ ∃ g : F.O, g * (Star.star F.e * F.f * F.e) = F.e

end GlobalTheory.Mum
