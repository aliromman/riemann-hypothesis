module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashToGLSmul
public import Mathlib.NumberTheory.ModularForms.Basic
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

@[expose] public section

open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices

private def toGLQ (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det ≠ 0) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ((Int.castRingHom ℚ).mapMatrix M)
    (by rw [← RingHom.map_det]; simpa using hM)

private lemma toGL_eq_map (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det ≠ 0) :
    toGL M = Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (toGLQ M hM) := by
  ext i j
  rw [toGL_val M hM]
  simp [toGLQ, Matrix.GeneralLinearGroup.map]

lemma isCusp_SL2Z_toGL_smul (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det ≠ 0) {c : OnePoint ℝ}
    (hc : IsCusp c 𝒮ℒ) : IsCusp (toGL M • c) 𝒮ℒ := by
  rw [isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨c, rfl⟩ := hc
  rw [toGL_eq_map M hM]
  exact ⟨toGLQ M hM • c, by rw [← Rat.coe_castHom, OnePoint.map_smul]⟩

theorem cuspAll_slash_toGL : ∀ (k : ℤ) (M : Matrix (Fin 2) (Fin 2) ℤ) (G : ℍ → ℂ), 0 < M.det →
    CuspAll k G → CuspAll k (G ∣[k] toGL M) := by
  intro k M G hM hG
  refine ⟨MDifferentiable.slash hG.1 k (toGL M), fun c hc => ?_⟩
  rw [← OnePoint.IsZeroAt.smul_iff]
  exact hG.2 _ (isCusp_SL2Z_toGL_smul M hM.ne' hc)

end GlobalTheory.HeckeFamilyMatrices
