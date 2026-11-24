module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.TraceQuot
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityNormalizedBorelJacquetUn
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

open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

theorem UpperTheory.Gal.Join.jacNorm :
    UpperTheory.Gal.Join.JacNorm := by
  intro k _ _ _ _ n V _ _ π t y
  rw [UnramFixed.jacB_apply, smul_smul]
  have h1 : ((((deltaHalf k fun _ : Fin n ↦ Unit).comp (leviTorus k (Fin n)).toMonoidHom) t : ℂˣ) : ℂ) =
      ((√(deltaB t) : ℝ) : ℂ) := by
    rw [MonoidHom.comp_apply, val_deltaHalf, deltaB_eq_modulus]
    rfl
  have h2 : ((√(deltaB t) : ℝ) : ℂ) ≠ 0 := by
    rw [← h1]
    exact Units.ne_zero _
  rw [Units.val_inv_eq_inv_val, h1, mul_inv_cancel₀ h2, one_smul]
