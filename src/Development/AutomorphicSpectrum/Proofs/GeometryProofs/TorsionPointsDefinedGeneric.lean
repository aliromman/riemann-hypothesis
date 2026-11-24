module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatLev
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
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.FarguesHodgeTate

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem level_parametrisation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (S : Scheme.{0}) (t : SAB H S) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ S) (n : ℕ), 1 ≤ n → 0 < D.p + D.q → IsProper (Limits.pullback.snd t.G.hom ξ) → (∀ (k : Type) [Field k] (f : Ω →+* k) (g : Over.mk (spMap f ≫ ξ) ⟶ t.G), g ^ n = 1 → ∃ x : Over.mk ξ ⟶ t.G, g.left = spMap f ≫ x.left) → (∀ (k : Type) [Field k] [IsAlgClosed k] (f : Ω →+* k), Nonempty (TateIso D k (Over.mk (spMap f ≫ ξ) ⟶ t.G) (fun a g => g ≫ t.act.act a) (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)))) → ∃ (ev : D.La → (Over.mk ξ ⟶ t.G)) (ζ₀ : Ωˣ), IsPrimitiveRoot ζ₀ n ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (f : Ω →+* k), ∃ I : TateIso D k (Over.mk (spMap f ≫ ξ) ⟶ t.G) (fun a g => g ≫ t.act.act a) (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)), (I.ζ n : k) = f ζ₀ ∧ ∀ a, (I.ev n a).left = spMap f ≫ (ev a).left :=
  @PositivityTheory.HtPt.Htat.level_param

end GlobalTheory.CompanionTheory.Ar.HT
