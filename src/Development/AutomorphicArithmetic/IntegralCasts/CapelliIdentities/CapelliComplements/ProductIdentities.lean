module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Lemma
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
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Lemmata.ProductIdentities.ProdInvZpowMulOfProdZpowEqOne

@[expose] public section

namespace Bl.ProductIdentities

private lemma prod_erase_one_perm_apply_eq_zero {n : Type} [Fintype n] [DecidableEq n] (σ : Equiv.Perm n) (hσ : σ ≠ 1)
    (k : n) : ∏ j ∈ Finset.univ.erase k, (1 : Matrix n n ℂ) (σ j) j = 0 := by
  have hex : ∃ j, j ≠ k ∧ σ j ≠ j := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    apply hσ
    ext x
    simp only [Equiv.Perm.coe_one, id_eq]
    by_cases hx : x = k
    · subst hx
      by_contra hk
      exact hk (σ.injective (h (σ x) hk))
    · exact h x hx
  obtain ⟨j, hjk, hj⟩ := hex
  apply Finset.prod_eq_zero (i := j) (Finset.mem_erase.mpr ⟨hjk, Finset.mem_univ _⟩)
  simp [hj]

end Bl.ProductIdentities
