module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.LocallyConstant.Basic
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

theorem UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker :
    ∀ {Γ C : Type} [inst : Group Γ]
    [inst_1 : TopologicalSpace Γ] [IsTopologicalGroup Γ] [inst_3 : Group C] (η : Γ →* C),
    IsOpen (↑η.ker : Set Γ) → IsLocallyConstant (⇑η : Γ → C) := by
  intro Γ C _ _ _ _ η h
  refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (η.ker : Set Γ),
    h.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · change x⁻¹ * x ∈ η.ker
    simp
  · intro y hy
    have hy' : η (x⁻¹ * y) = 1 := hy
    rw [map_mul, map_inv] at hy'
    exact (inv_mul_eq_one.mp hy').symm
