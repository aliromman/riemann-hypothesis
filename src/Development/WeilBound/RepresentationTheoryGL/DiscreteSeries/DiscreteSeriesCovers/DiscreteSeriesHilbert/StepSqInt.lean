module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumEmbeddingMemHlam
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

noncomputable section

namespace PositivityTheory.RgDs.Hilb

open ReciprocityTheory.ChartRestriction.DS

def StepSig : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (T : S7.KType ε (lowK ε lam))
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)), IsPsiFor ε lam T Ψ →
      (∀ g ∈ UJset ε, ∀ x ∈ Hlam ε Ψ T.w, rreg ε g x ∈ Hlam ε Ψ T.w) →
      (∀ g ∈ UJset ε, ∀ x : Hlam ε Ψ T.w, ((sigLam ε Ψ T.w g x : Hlam ε Ψ T.w) : L2 ε) = rreg ε g x) ∧
        IsURepOn (UJset ε) (sigLam ε Ψ T.w) ∧ Nontrivial (Hlam ε Ψ T.w)

def StepSqInt : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (T : S7.KType ε (lowK ε lam))
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)), IsPsiFor ε lam T Ψ →
      (∀ g ∈ UJset ε, ∀ x ∈ Hlam ε Ψ T.w, rreg ε g x ∈ Hlam ε Ψ T.w) →
      (∀ g ∈ UJset ε, ∀ v v' : T.V,
        inner ℂ (uniformisationL2 ε Ψ T.w v') (rreg ε g (uniformisationL2 ε Ψ T.w v)) =
          ((‖uniformisationL2 ε Ψ T.w T.w‖ ^ 2 : ℝ) : ℂ) * inner ℂ v' (Ψ g v)) →
      Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) (sigLam ε Ψ T.w) →
      Formalism.MainNotions.S.IsSqIntOn ε (sigLam ε Ψ T.w)

end PositivityTheory.RgDs.Hilb
