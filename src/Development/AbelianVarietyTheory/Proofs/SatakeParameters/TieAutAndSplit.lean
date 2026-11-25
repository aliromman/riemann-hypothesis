module

public import Formalism.LocalToGlobal.UnitaryNorms.CharTied
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import ReciprocityTheory.Automorphisms.PlaceA

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin

namespace GlobalTheory.AutomorphismSplitting

theorem isCSD_inv' {R : Ranks} {H : Host R} {χ : HChar H.E} (h : IsCSD H χ) : IsCSD H χ⁻¹ :=
  ⟨fun w w' hw k => congrArg (·⁻¹) (h.1 w w' hw k), fun k => congrArg (·⁻¹) (h.2 k)⟩

theorem hasInf_inv {L : Type} [Field L] [NumberField L] {I : Type} [Fintype I] {φ : I → L →+* ℂ} {χ : HChar L}
    (h : χ.HasInf φ (fun _ => 1)) : (χ⁻¹).HasInf φ (fun _ => -1) := by
  intro k
  have hk := h k
  show (((χ.inf k)⁻¹ : ℂˣ) : ℂ) = _
  rw [Units.val_inv_eq_inv_val, hk, ← Finset.prod_inv_distrib]
  simp

end GlobalTheory.AutomorphismSplitting
