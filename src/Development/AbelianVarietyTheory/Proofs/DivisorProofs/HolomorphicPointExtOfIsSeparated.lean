module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FderivFnCongr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointHol
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem point_hol_ext_of_isSeparated : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Opens E) {X : Scheme.{0}}, X.IsSeparated → ∀ x x' : Sp (Hol W) ⟶ X, (∀ (p : E) (hp : p ∈ W), spMap (Hol.ev p hp).toRingHom ≫ x = spMap (Hol.ev p hp).toRingHom ≫ x') → x = x' := by
  intro E _ _ W X hX x x' h
  have : IsSeparated (terminal.from X) := hX.isSeparated_terminal_from
  exact point_hol_ext E W X (⊤_ Scheme) (terminal.from X) x x' (terminal.hom_ext _ _) h

end GlobalTheory.AnPer
