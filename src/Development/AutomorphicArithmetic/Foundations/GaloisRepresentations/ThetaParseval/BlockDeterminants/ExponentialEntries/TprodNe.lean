module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

open scoped TensorProduct

theorem UpperTheory.TP.RP.tprodNe :
    ∀ {ι : Type} [Fintype ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] (f : ∀ i, V i), (∀ i, f i ≠ 0) → PiTensorProduct.tprod ℂ f ≠ 0 := by
  intro ι _ V _ _ f hf h
  have hex : ∀ i, ∃ l : Module.Dual ℂ (V i), l (f i) ≠ 0 := fun i => by
    by_contra hc
    push_neg at hc
    exact hf i ((Module.forall_dual_apply_eq_zero_iff ℂ (f i)).1 hc)
  choose l hl using hex
  have h0 := congrArg
    (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap l)) h
  rw [PiTensorProduct.lift.tprod, map_zero, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply] at h0
  obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.1 h0
  exact hl i hi
