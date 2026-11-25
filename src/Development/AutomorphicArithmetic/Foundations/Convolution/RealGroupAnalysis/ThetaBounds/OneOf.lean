module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.NormInf
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

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.oneOf :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (_D : Dat F E), OneOf F E := by
  intro F E _ _ _ _ _ _ _ D y hy
  obtain ⟨u, hu, hn⟩ := normInf F E D (Matrix.GeneralLinearGroup.det y)
  have hu1 : u = 1 := by
    refine Units.ext (funext fun v => ?_)
    rw [hu v]
    have h1 : ∀ w : InfinitePlace E, ‖(Matrix.GeneralLinearGroup.det y).val w‖ = 1 := hy
    change _ = (1 : ℝ)
    refine Finset.prod_eq_one fun w _ => ?_
    split_ifs
    · rw [h1 w, one_pow]
    · rfl
  change ideleNorm F E (Matrix.GeneralLinearGroup.det (infGL E 2 y)) = 1
  rw [det_infGL, hn, hu1, map_one]
