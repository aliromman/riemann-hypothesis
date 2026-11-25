module

public import Formalism.LocalRingCardinality.DataTheta
public import Mathlib.RingTheory.PiTensorProduct
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DblCol
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap

@[expose] public section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

namespace GlobalTheory

theorem tprod_one_pol_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (P Q R S : ℕ),
    (PiTensorProduct.tprod ℂ fun _ : InfinitePlace F => (1 : Formalism.BasicNotions.TH.Pol P Q R S)) ≠ 0 := by
  intro F _ _ P Q R S h
  let c : Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] ℂ := (MvPolynomial.aeval (fun _ => (0:ℂ))).toLinearMap
  have key := congrArg (PiTensorProduct.lift
      ((MultilinearMap.mkPiAlgebra ℂ (InfinitePlace F) ℂ).compLinearMap (fun _ => c))) h
  simp [PiTensorProduct.lift.tprod, c] at key

end GlobalTheory
