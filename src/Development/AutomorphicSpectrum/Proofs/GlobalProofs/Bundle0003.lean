module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PrimePowerNotDvdDifferent

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.BlockBasisChangeEntriesStatement
section
open Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_form_change_of_basis_lie : ∀ {n n' : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (H' : Matrix (Fin n') (Fin n') ℂ) (J : Matrix (Fin n) (Fin n') ℂ),
    Hᴴ = H → H'ᴴ = H' → IsUnit H.det → IsUnit H'.det → Jᴴ * H * J = H' →
    ((H'⁻¹ * Jᴴ * H) * J = 1 ∧
      (∀ Z : Matrix (Fin n') (Fin n') ℂ, -(H⁻¹ * (J * Z * (H'⁻¹ * Jᴴ * H))ᴴ * H) = J * (-(H'⁻¹ * Zᴴ * H')) * (H'⁻¹ * Jᴴ * H)) ∧
      (∀ A : Matrix (Fin n') (Fin n') ℂ, Aᴴ * H' + H' * A = 0 →
        (J * A * (H'⁻¹ * Jᴴ * H))ᴴ * H + H * (J * A * (H'⁻¹ * Jᴴ * H)) = 0) ∧
      (∀ (A : Matrix (Fin n') (Fin n') ℂ) (t : ℝ), NormedSpace.exp (t • (J * A * (H'⁻¹ * Jᴴ * H))) * J = J * NormedSpace.exp (t • A)) ∧
      (∀ (A : Matrix (Fin n') (Fin n') ℂ) (t : ℝ) (x : Fin n → ℂ), (Jᴴ * H) *ᵥ x = 0 →
        NormedSpace.exp (t • (J * A * (H'⁻¹ * Jᴴ * H))) *ᵥ x = x)) := by
  first | exact @GlobalTheory.CompanionTheory.IsometricMatrix.main | exact GlobalTheory.CompanionTheory.IsometricMatrix.main | (intros; apply GlobalTheory.CompanionTheory.IsometricMatrix.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.PrimePowerNotDvdDifferentStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prime_power_not_dvd_different : ∀ (E : Type) [Field E] [NumberField E] (P J : Ideal (𝓞 E)) [P.IsPrime] (p k : ℕ), p.Prime → (p : 𝓞 E) ∈ P → ¬ P ∣ J → Ideal.span {((p : 𝓞 E)) ^ (Module.finrank ℚ E)} = P ^ k * J → ¬ P ^ k ∣ differentIdeal ℤ (𝓞 E) := by
  first | exact @GlobalTheory.CompanionTheory.Glob.not_pow_dvd_different | exact GlobalTheory.CompanionTheory.Glob.not_pow_dvd_different | (intros; apply GlobalTheory.CompanionTheory.Glob.not_pow_dvd_different <;> assumption)
end

