module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.Finsupp.Weight
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

noncomputable def UpperTheory.Reformulated.B.Qf22.biHom :
    {K ι κ : Type} → [inst : Field K] → ℕ → MvPolynomial κ (MvPolynomial ι K) → Prop :=
    fun {K ι κ : Type} [Field K] (d : ℕ) (F : MvPolynomial κ (MvPolynomial ι K)) ↦
      ∀ (β : κ →₀ ℕ) (n : ι →₀ ℕ),
        AddMonoidAlgebra.coeff (AddMonoidAlgebra.coeff F β) n ≠ (0 : K) →
          (Finsupp.degree : (ι →₀ ℕ) → ℕ) n + (Finsupp.degree : (κ →₀ ℕ) → ℕ) β = d

theorem UpperTheory.Reformulated.B.Qf22.biHom_sum.{u_1} :
    ∀ {K ι κ : Type} [inst : Field K] [Fintype κ] {α : Type u_1} {d : ℕ} (s : Finset α)
      (F : α → MvPolynomial κ (MvPolynomial ι K)),
      (∀ a ∈ s, UpperTheory.Reformulated.B.Qf22.biHom d (F a)) → UpperTheory.Reformulated.B.Qf22.biHom d (∑ a ∈ s, F a) := by
  intro K ι κ _ _ α d s F h β n hne
  rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_sum] at hne
  obtain ⟨a, ha, hna⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  exact h a ha β n hna
