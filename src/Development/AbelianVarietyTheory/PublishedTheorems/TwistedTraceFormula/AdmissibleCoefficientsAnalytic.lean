module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
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

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd
open scoped InnerProductSpace

namespace GlobalTheory.Published

def AdmissibleCoefficientsAnalytic : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsAdmRep ε π →
    ∀ v w : H, IsKFin ε π v → IsKFin ε π w → AnalyticOnUJ ε fun g => ⟪w, π g v⟫_ℂ

def LeviSubmoduleDense : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Flag n a), IsIsoFlag ε j W → (∀ i, 1 ≤ j i) →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
      (σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)), IsURepOn (mats (leviOne ε W)) σ → IsIrredOn (mats (leviOne ε W)) σ →
      ∀ S : Submodule ℂ V, S ≠ ⊥ → (∀ v ∈ S, IsKFinIn (leviOne ε W) σ v) →
        (∀ X : Matrix (Fin n) (Fin n) ℂ, (∀ t : ℝ, NormedSpace.exp (t • X) ∈ mats (leviOne ε W)) →
          ∀ v ∈ S, ∃ v' ∈ S, HasDerivAt (fun t : ℝ => σ (NormedSpace.exp (t • X)) v) v' 0) →
        Dense (S : Set V)

def HarishChandraAnalyticity : Prop := AdmissibleCoefficientsAnalytic ∧ LeviSubmoduleDense

end GlobalTheory.Published

end
