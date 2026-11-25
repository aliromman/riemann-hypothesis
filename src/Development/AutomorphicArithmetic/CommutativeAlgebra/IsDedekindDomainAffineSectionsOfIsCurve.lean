module

public import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField
public import Development.EtaleCohomology.EtaleSheaves.ProperLineCovers.CoverPf
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.RingTheory.KrullDimension.Field
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
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.IsChart
import GroundTheory.FunctionField.PlaceDefs

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

private theorem not_isField_of_curve {k : Type} [Field k] {C : Scheme.{0}} (c : C ⟶ Sp k) (hc : IsCurve c)
    (W : C.Opens) (hW : IsAffineOpen W) (hWn : (W : Set C).Nonempty) : ¬ IsField Γ(C, W) := by
  intro hF
  have h := CurveCut.CoverPf.krullDim_eq_one c hc W hW hWn
  rw [ringKrullDim_eq_zero_of_isField hF] at h
  norm_num at h

private theorem stalk_isIntegrallyClosed {k : Type} [Field k] [IsAlgClosed k] {C : Scheme.{0}} (c : C ⟶ Sp k)
    (hc : IsCurve c) (y : C) : IsIntegrallyClosed (C.presheaf.stalk y) := by
  haveI := hc.1
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) (by simp)
  have hne : (U : Set C).Nonempty := ⟨y, hyU⟩
  haveI : Nonempty U := ⟨⟨y, hyU⟩⟩
  haveI : IsIntegrallyClosed Γ(C, U) := CurveCut.CoverPf.leafNormal _ c hc U hU hne
  letI : Algebra Γ(C, U) (C.presheaf.stalk y) := C.presheaf.algebra_section_stalk ⟨y, hyU⟩
  haveI := hU.isLocalization_stalk ⟨y, hyU⟩
  exact isIntegrallyClosed_of_isLocalization _ (hU.primeIdealOf ⟨y, hyU⟩).asIdeal.primeCompl
    (Ideal.primeCompl_le_nonZeroDivisors _)

theorem UpperTheory.isDedekindDomain_affine_sections_of_isCurve :
    ∀ (k : Type) [Field k] [IsAlgClosed k] {C : Scheme.{0}} (c : C ⟶ Sp k), IsCurve c → (∀ W : C.Opens, IsAffineOpen W → (W : Set C).Nonempty → IsDedekindDomain Γ(C, W) ∧ ¬ IsField Γ(C, W)) ∧ ∀ y : C, IsIntegrallyClosed (C.presheaf.stalk y) := by
  intro k _ _ C c hc
  refine ⟨fun W hW hWn => ⟨?_, not_isField_of_curve c hc W hW hWn⟩, stalk_isIntegrallyClosed c hc⟩
  exact LateralTheory.E.E4.CurveCut.CoverPf.LeafDedRing_of LateralTheory.E.E4.CurveCut.CoverPf.leafDim1
    LateralTheory.E.E4.CurveCut.CoverPf.leafNormal k c hc W hW hWn
