module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
public import Mathlib.LinearAlgebra.Lagrange
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
public import Mathlib.Algebra.Algebra.StrictPositivity
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital

@[expose] public section

open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator MatrixOrder

namespace GlobalTheory

theorem posDef_conjTranspose_mul_self_eq_exp_polynomial :
    ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) ℂ), IsUnit g →
      ∃ (L : Matrix (Fin n) (Fin n) ℂ) (p : Polynomial ℂ),
        Lᴴ = L ∧ NormedSpace.exp L = gᴴ * g ∧ L = Polynomial.aeval (gᴴ * g) p := by
  intro n g hg
  set h : Matrix (Fin n) (Fin n) ℂ := gᴴ * g with hh
  have hpd : h.PosDef :=
    Matrix.PosDef.conjTranspose_mul_self g (Matrix.mulVec_injective_iff_isUnit.mpr hg)
  have hsp : IsStrictlyPositive h := hpd.isStrictlyPositive
  have hsa : IsSelfAdjoint h := hpd.isHermitian
  have hfin : (spectrum ℝ h).Finite := Matrix.finite_real_spectrum
  classical
  let s : Finset ℝ := hfin.toFinset
  let q : Polynomial ℝ := Lagrange.interpolate s id Real.log
  have hq : ∀ x ∈ spectrum ℝ h, q.eval x = Real.log x := by
    intro x hx
    have hxs : x ∈ s := hfin.mem_toFinset.mpr hx
    exact Lagrange.eval_interpolate_at_node (r := Real.log) (Set.injOn_id _) hxs
  refine ⟨CFC.log h, q.map (algebraMap ℝ ℂ), ?_, CFC.exp_log h hsp, ?_⟩
  · have : IsSelfAdjoint (CFC.log h) := by
      unfold CFC.log; exact cfc_predicate _ _
    exact this
  · rw [Polynomial.aeval_map_algebraMap, ← cfc_polynomial q h]
    unfold CFC.log
    exact cfc_congr (fun x hx => (hq x hx).symm)

end GlobalTheory
