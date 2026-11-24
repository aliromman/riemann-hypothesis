module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLiftsSqZeroClassifiedByDifferentials
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.algHom_lifts_sqZero_classified_by_differentials : ∀ (R R₀ B B₀ B' : Type) [CommRing R] [CommRing R₀] [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] [CommRing B'] [Algebra R B'] (I : Ideal R), I ^ 2 = 0 → ∀ (π : R →+* R₀), Function.Surjective π → ∀ p : B →+* B₀, SemiHom π p → Function.Surjective p → (∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) → ∀ α : B →ₐ[R] B', (∀ β : B →ₐ[R] B', (∀ b, α b - β b ∈ I.map (algebraMap R B')) → ∃! θ : Ω[B₀⁄R₀] →+ B', IsTheta I p α β θ) ∧ ∀ θ : Ω[B₀⁄R₀] →+ B', (∀ b w, θ (p b • w) = α b * θ w) → (∀ w, θ w ∈ I.map (algebraMap R B')) → ∃ β : B →ₐ[R] B', IsTheta I p α β θ := by
  first | exact @GlobalTheory.LiftSys.theta_classify
