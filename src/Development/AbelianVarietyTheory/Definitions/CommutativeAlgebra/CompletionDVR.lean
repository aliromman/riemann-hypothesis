module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
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
import Mathlib.Tactic.TypeStar

@[expose] public section

namespace ReciprocityTheory.CA.Pt

open IsLocalRing

theorem completionDVR (W : Type*) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] :
    (∃ _ : IsDomain (AdicCompletion (maximalIdeal W) W),
      IsDiscreteValuationRing (AdicCompletion (maximalIdeal W) W)) ∧
    IsAdicComplete (maximalIdeal (AdicCompletion (maximalIdeal W) W)) (AdicCompletion (maximalIdeal W) W) ∧
    Function.Injective (algebraMap W (AdicCompletion (maximalIdeal W) W)) ∧
    IsLocalHom (algebraMap W (AdicCompletion (maximalIdeal W) W)) ∧
    maximalIdeal (AdicCompletion (maximalIdeal W) W) =
      (maximalIdeal W).map (algebraMap W (AdicCompletion (maximalIdeal W) W)) :=
  ⟨⟨inferInstance, inferInstance⟩, inferInstance, GlobalTheory.algebraMap_adicCompletion_injective_of_dvr W, inferInstance,
    AdicCompletion.maximalIdeal_eq_map⟩

end ReciprocityTheory.CA.Pt
