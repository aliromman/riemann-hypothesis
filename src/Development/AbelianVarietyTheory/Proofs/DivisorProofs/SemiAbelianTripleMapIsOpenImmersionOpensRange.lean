module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

namespace GlobalTheory

theorem sabMap_isOpenImmersion_opensRange (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (j : X' ⟶ X) [IsOpenImmersion j] (m : SABMap t' t j) : ∃ _ : IsOpenImmersion m.φ, m.φ.opensRange = t.G.hom ⁻¹ᵁ j.opensRange := by
  have h : IsPullback m.φ t'.G.hom t.G.hom j := m.cart.1
  have hφ : m.φ = h.isoPullback.hom ≫ pullback.fst t.G.hom j := by simp
  have hi : IsOpenImmersion m.φ := by rw [hφ]; infer_instance
  refine ⟨hi, ?_⟩
  ext1
  have h1 : Set.range m.φ = Set.range (pullback.fst t.G.hom j) := by
    rw [hφ, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Set.range_eq_univ.mpr h.isoPullback.hom.surjective, Set.image_univ]
  simpa [h1] using Scheme.Pullback.range_fst t.G.hom j
end GlobalTheory
