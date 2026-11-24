module

import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLLieF
public import Mathlib.Algebra.Lie.Classical
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Exponential

@[expose] public section

open scoped Matrix

namespace GlobalTheory.RealWeil

theorem mem_sp_of_exp_mem_symplecticGroup (l : Type) [Fintype l] [DecidableEq l]
    (X : Matrix (l ⊕ l) (l ⊕ l) ℝ)
    (h : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ Matrix.symplecticGroup l ℝ) :
    X ∈ LieAlgebra.Symplectic.sp l ℝ := by
  apply PositivityTheory.RL.Up.mem_lie_of <;> assumption

end GlobalTheory.RealWeil
