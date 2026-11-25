module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVectorsSubspaceStableSobolevFormDeriv
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

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.smoothVectors_subspace_stable_sobolevForm_deriv : ∀ (n : ℕ) (Hm : Mt n) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mt n → (H →L[ℂ] H)), Hm.IsHermitian → Hm.det ≠ 0 → IsURepOn (Formalism.QuantumDeterminants.UH Hm) σ → (∀ v ∈ Submodule.span ℂ {w | SmoothVec (lieH Hm) σ w}, SmoothVec (lieH Hm) σ v) ∧ ∀ v, SmoothVec (lieH Hm) σ v → (∀ g ∈ Formalism.QuantumDeterminants.UH Hm, SmoothVec (lieH Hm) σ (σ g v)) ∧ (∀ X ∈ lieH Hm, SmoothVec (lieH Hm) σ (dRep σ X v) ∧ HasDerivAt (fun t : ℝ => σ (NormedSpace.exp (t • X)) v) (dRep σ X v) 0) ∧ (∀ Z, SmoothVec (lieH Hm) σ (dRepC Hm σ Z v)) ∧ ∀ ℓ : H →ₗ[ℂ] ℂ, Sobolev₂ (lieH Hm) σ ℓ → ∀ X ∈ lieH Hm, HasDerivAt (fun t : ℝ => ℓ (σ (NormedSpace.exp (t • X)) v)) (ℓ (dRep σ X v)) 0 := by
  first | exact @GlobalTheory.UnitarySmVec.smoothVec_basic
