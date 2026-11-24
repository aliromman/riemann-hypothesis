module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.chart_of :
    Chart := by
  intro Z S p _ A _ u
  haveI : IsAffine (pullback p u) := isAffine_of_isAffineHom (pullback.snd p u)
  let V := pullback p u
  let e : Spec Γ(V, ⊤) ≅ V := V.isoSpec.symm
  let φ : CommRingCat.of A ⟶ Γ(V, ⊤) := Spec.preimage (e.hom ≫ pullback.snd p u)
  have hφ : Spec.map φ = e.hom ≫ pullback.snd p u := Spec.map_preimage _
  letI alg : Algebra A Γ(V, ⊤) := φ.hom.toAlgebra
  have hφ' : Spec.map (CommRingCat.ofHom (algebraMap A Γ(V, ⊤))) = e.hom ≫ pullback.snd p u := hφ
  refine ⟨Γ(V, ⊤), inferInstance, alg, e.hom ≫ pullback.fst p u, ?_, ?_⟩
  · have hfin : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap A Γ(V, ⊤)))) := by
      rw [hφ']; infer_instance
    have h2 := (IsFinite.SpecMap_iff _).1 hfin
    exact RingHom.finite_algebraMap.1 h2
  · rw [hφ']
    exact IsPullback.of_iso (IsPullback.of_hasPullback p u) e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp)
