module

public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ThetaReal

def UnivBasis {S : Scheme.{0}} (P : PolAV S) (n : ℤ) {T₀ : Over S} {κ : Type} (b : κ → SecM P.A P.L n T₀) : Prop :=
  ∀ (T : Over S) [IsAffine T.left] (h : T ⟶ T₀), ∃ c : Module.Basis κ Γ(T.left, ⊤) (SecM P.A P.L n T),
    ∀ i, c i = VVRank.pullM P.A P.L n h (b i)

theorem exists_univBasis (h : SecBaseChangeAnySt) {S : Scheme.{0}} (P : PolAV S) (n : ℕ) (hn : 1 ≤ n) (p : S) :
    ∃ V : S.Opens, p ∈ V ∧ ∃ b : Fin (n ^ P.g) → SecM P.A P.L n (overRes (T := baseOver S) V), UnivBasis P n b := by
  obtain ⟨V, hV, b, hb⟩ := h S P n hn p
  exact ⟨V, hV, fun i => SecM.ofSec P.A (b i), fun T _ h => VVRank.exists_basis P n b hb T h⟩

end GlobalTheory.ThetaReal
end
