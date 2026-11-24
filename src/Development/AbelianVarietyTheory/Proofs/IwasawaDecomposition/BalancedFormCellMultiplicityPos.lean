module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotIsPrimZero
import Mathlib.GroupTheory.FiniteAbelian.Basic
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem cellMult_pos {O : Type} [CommRing O] [Module.Finite ℤ O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m : ℕ} (δ : Fin m → balForms bar X) : 0 < cellMult bar δ := by
  haveI : Module.Finite ℤ X := Module.Finite.trans O X
  unfold cellMult
  set M := balForms bar X ⧸ Submodule.span ℤ (Set.range δ)
  set T := Submodule.torsion ℤ M
  haveI : IsNoetherian ℤ (LinearMap.BilinForm ℤ X) := inferInstance
  haveI : Module.Finite ℤ M := inferInstance
  haveI : IsNoetherian ℤ M := inferInstance
  haveI : IsNoetherian ℤ T := isNoetherian_of_submodule_of_noetherian ℤ M T inferInstance
  haveI : Module.Finite ℤ T := ⟨IsNoetherian.noetherian ⊤⟩
  haveI : AddGroup.FG T := by
    rw [← Module.Finite.iff_addGroup_fg]; infer_instance
  haveI : Finite T := by
    apply AddCommGroup.finite_of_fg_torsion
    rintro ⟨x, hx⟩
    obtain ⟨⟨a, ha⟩, hax⟩ := hx
    refine (isOfFinAddOrder_iff_zsmul_eq_zero).2 ⟨a, nonZeroDivisors.ne_zero ha, ?_⟩
    ext
    exact hax
  exact Nat.card_pos

end GlobalTheory.PolFan
