module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaLiftTrivialOrbitTermsVanish
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.FromGL
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
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.iwa :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], ∀ g : G1 F, ∃ (b : A F) (a : (A F)ˣ), ∃ k ∈ KK F, g = nU b * mD a * k := by
  intro F _ _ _ g
  obtain ⟨b, hb, k, hk, e⟩ := Reduction.exists_adelicBorel_mul_maxCompact (K := F) (n := 2) (gl g)
  obtain ⟨x, a, k', hk', hg, -, -⟩ := UpperTheory.ConvolutionTheory.R2.M.fromGL F g b hb k hk e
  exact ⟨x, a, k', hk', hg⟩
