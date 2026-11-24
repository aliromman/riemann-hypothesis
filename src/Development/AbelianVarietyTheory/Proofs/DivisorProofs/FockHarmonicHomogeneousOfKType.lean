module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousOfDense
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsSubOfDisjoint
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

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.FockAlg


open GlobalTheory.JointHarm GlobalTheory.FockSeq in
theorem harmonic_homog_of_type : ∀ (p q r s : ℕ),
    (∀ (μ : Ix p q → ℚ) (P : Pol p q r s), P ≠ 0 → OfType (fockAct1 p q r s) μ P →
      P ∈ harm1 p q r s →
      ∃ d : ℕ, (d : ℚ) = degW (cPair r s) μ ∧ P ∈ homog (Ix p q × Ix r s) d) ∧
    (∀ (μ : Ix r s → ℚ) (P : Pol p q r s), P ≠ 0 → OfType (fockAct2 p q r s) μ P →
      P ∈ harm2 p q r s →
      ∃ d : ℕ, (d : ℚ) = degW (cPair p q) μ ∧ P ∈ homog (Ix p q × Ix r s) d) :=
  fun _ _ _ _ =>
    ⟨fun _ P h0 ht hh => isSide_one.homog_of_type isFockIsometry_embedding emb_injective
        Function.bijective_id h0 ht ((mem_harm1 P).1 hh),
      fun _ P h0 ht hh => isSide_two.homog_of_type isFockIsometry_embedding emb_injective
        Prod.swap_bijective h0 ht ((mem_harm2 P).1 hh)⟩

end GlobalTheory.FockAlg
