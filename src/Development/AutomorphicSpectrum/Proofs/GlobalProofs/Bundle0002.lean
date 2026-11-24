module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdaptedFrameOrthogonalSubspaceStatement
section
open Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_basis_change_entries : ∀ (n n' a : ℕ) (hdim : a + n' + a = n) (P : Matrix (Fin n) (Fin n) ℂ), IsUnit P.det →
    ∀ (J : Matrix (Fin n) (Fin n') ℂ) (Jp : Matrix (Fin n') (Fin n) ℂ) (B Bi : Matrix (Fin n') (Fin n') ℂ), Jp * J = 1 → B * Bi = 1 →
    (∀ (i : Fin n) (j : Fin n'), J i j = ∑ r : Fin n', P i (⟨a + r.val, by omega⟩ : Fin n) * B r j) →
    (∀ b : Fin n, (b.val < a ∨ n ≤ b.val + a) → Jp *ᵥ (fun k => P k b) = 0) →
    ∀ p q : Fin n', J * Matrix.single p q (1 : ℂ) * Jp = ∑ r : Fin n', ∑ u : Fin n', (B r p * Bi q u) •
      (P * Matrix.single (⟨a + r.val, by omega⟩ : Fin n) (⟨a + u.val, by omega⟩ : Fin n) (1 : ℂ) * P⁻¹) := by
  first | exact @GlobalTheory.CompanionTheory.MidConj.conj_units_of_mid | exact GlobalTheory.CompanionTheory.MidConj.conj_units_of_mid | (intros; apply GlobalTheory.CompanionTheory.MidConj.conj_units_of_mid <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.BlockBasisChangeEntries
section
open Matrix

namespace GlobalTheory.CompanionTheory.IsometricMatrix

theorem exp_mulVec_of_mulVec_eq_zero {m : ℕ} (N : Matrix (Fin m) (Fin m) ℂ) (x : Fin m → ℂ)
    (hx : N *ᵥ x = 0) : NormedSpace.exp N *ᵥ x = x := by
  have hC : N * Matrix.replicateCol (Fin 1) x = Matrix.replicateCol (Fin 1) x * (0 : Matrix (Fin 1) (Fin 1) ℂ) := by
    ext i j
    have hi := congrFun hx i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hi
    simpa [Matrix.mul_apply, Matrix.replicateCol] using hi
  have hE := matrix_exp_mul_eq_mul_exp_of_intertwine N _ 0 hC
  simp only [NormedSpace.exp_zero, Matrix.mul_one] at hE
  ext i
  have hi := congrFun (congrFun hE i) 0
  simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.replicateCol] using hi

theorem main {n n' : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (H' : Matrix (Fin n') (Fin n') ℂ)
    (J : Matrix (Fin n) (Fin n') ℂ)
    (hH : Hᴴ = H) (hH' : H'ᴴ = H') (hd : IsUnit H.det) (hd' : IsUnit H'.det)
    (hJ : Jᴴ * H * J = H') :
    ((H'⁻¹ * Jᴴ * H) * J = 1 ∧
      (∀ Z : Matrix (Fin n') (Fin n') ℂ, -(H⁻¹ * (J * Z * (H'⁻¹ * Jᴴ * H))ᴴ * H) = J * (-(H'⁻¹ * Zᴴ * H')) * (H'⁻¹ * Jᴴ * H)) ∧
      (∀ A : Matrix (Fin n') (Fin n') ℂ, Aᴴ * H' + H' * A = 0 →
        (J * A * (H'⁻¹ * Jᴴ * H))ᴴ * H + H * (J * A * (H'⁻¹ * Jᴴ * H)) = 0) ∧
      (∀ (A : Matrix (Fin n') (Fin n') ℂ) (t : ℝ), NormedSpace.exp (t • (J * A * (H'⁻¹ * Jᴴ * H))) * J = J * NormedSpace.exp (t • A)) ∧
      (∀ (A : Matrix (Fin n') (Fin n') ℂ) (t : ℝ) (x : Fin n → ℂ), (Jᴴ * H) *ᵥ x = 0 →
        NormedSpace.exp (t • (J * A * (H'⁻¹ * Jᴴ * H))) *ᵥ x = x)) := by
  have hJ' : Jᴴ * (H * J) = H' := by rw [← Matrix.mul_assoc]; exact hJ
  have hPJ : H'⁻¹ * Jᴴ * H * J = 1 := by
    simp only [Matrix.mul_assoc]
    rw [hJ', Matrix.nonsing_inv_mul _ hd']
  have hPs : (H'⁻¹ * Jᴴ * H)ᴴ = H * J * H'⁻¹ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_nonsing_inv, hH, hH', Matrix.mul_assoc]
  refine ⟨hPJ, fun Z => ?_, fun A hA => ?_, fun A t => ?_, fun A t x hx => ?_⟩
  · rw [Matrix.conjTranspose_mul (J * Z) (H'⁻¹ * Jᴴ * H), hPs, Matrix.conjTranspose_mul J Z]
    simp only [Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg,
      Matrix.nonsing_inv_mul_cancel_left _ _ hd, Matrix.mul_nonsing_inv_cancel_left _ _ hd']
  · have key : H * J * H'⁻¹ * (Aᴴ * H' + H' * A) * (H'⁻¹ * Jᴴ * H) =
        (J * A * (H'⁻¹ * Jᴴ * H))ᴴ * H + H * (J * A * (H'⁻¹ * Jᴴ * H)) := by
      rw [Matrix.conjTranspose_mul (J * A) (H'⁻¹ * Jᴴ * H), hPs, Matrix.conjTranspose_mul J A,
        Matrix.mul_add, Matrix.add_mul]
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hd',
        Matrix.mul_nonsing_inv_cancel_left _ _ hd']
    rw [← key, hA, Matrix.mul_zero, Matrix.zero_mul]
  · have hBJ : J * A * (H'⁻¹ * Jᴴ * H) * J = J * A := by
      rw [Matrix.mul_assoc, hPJ, Matrix.mul_one]
    exact matrix_exp_smul_mul_eq_mul_exp_smul_of_intertwine n n' _ J A hBJ t
  · have hB : (J * A * (H'⁻¹ * Jᴴ * H)) *ᵥ x = 0 := by
      have hfac : J * A * (H'⁻¹ * Jᴴ * H) = (J * A * H'⁻¹) * (Jᴴ * H) := by
        simp only [Matrix.mul_assoc]
      rw [hfac, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
    apply exp_mulVec_of_mulVec_eq_zero
    rw [Matrix.smul_mulVec, hB, smul_zero]

end GlobalTheory.CompanionTheory.IsometricMatrix
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.RamifiedPrimeContainsDiscriminantStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramified_prime_contains_discriminant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (S : Finset (HeightOneSpectrum (𝓞 F))), (∀ v ∉ S, Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal) → ∀ (P : Ideal (𝓞 E)) [P.IsPrime], P ≠ ⊥ → P ∣ differentIdeal ℤ (𝓞 E) → (((discr F).natAbs * ∏ v ∈ S, v.asIdeal.absNorm : ℕ) : 𝓞 E) ∈ P := by
  first | exact @GlobalTheory.CompanionTheory.GlobalFiniteness.natAbs_discr_mul_prod_absNorm_mem_of_dvd_differentIdeal | exact GlobalTheory.CompanionTheory.GlobalFiniteness.natAbs_discr_mul_prod_absNorm_mem_of_dvd_differentIdeal | (intros; apply GlobalTheory.CompanionTheory.GlobalFiniteness.natAbs_discr_mul_prod_absNorm_mem_of_dvd_differentIdeal <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SkewOperatorBoundedByPolynomialRootsStatement
section
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.skew_operator_bounded_by_polynomial_roots :
    ∀ (M H : Type) [AddCommGroup M] [Module ℂ M] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (ι : M →ₗ[ℂ] H), Function.Injective ι → ∀ T : Module.End ℂ M,
      (∀ x y, ⟪ι (T x), ι y⟫_ℂ = -⟪ι x, ι (T y)⟫_ℂ) →
      ∀ m : Polynomial ℂ, m ≠ 0 → ∀ κ : ℝ, 0 ≤ κ → (∀ r ∈ m.roots, ‖r‖ ≤ κ) →
      ∀ x, Polynomial.aeval T m x = 0 → ‖ι (T x)‖ ≤ κ * ‖ι x‖ :=
  GlobalTheory.CompanionTheory.SkewSpec.norm_le_of_aeval_eq_zero
end

