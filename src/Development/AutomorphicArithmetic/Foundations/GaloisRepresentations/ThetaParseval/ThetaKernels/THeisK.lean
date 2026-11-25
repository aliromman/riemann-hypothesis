module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
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



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
def TUnit_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ ν : Measure (Mx F E d.m d.n), ν.IsAddHaarMeasure → ∀ x, ∀ Φ ∈ d.sch, ∀ Φ' ∈ d.sch,
  ∫ X, d.T (d.om x Φ) X * star (d.T (d.om x Φ') X) ∂ν = ∫ X, d.T Φ X * star (d.T Φ' X) ∂ν
def THeis_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ Φ ∈ d.sch, ∀ Z X : Mx F E d.m d.n,
  d.T (d.dd.rho d.B.ψ (Z * (incM F d.b.1.toCols₂)ᵀ) Φ) X = d.T Φ (X + Z) ∧
  d.T (d.dd.rho d.B.ψ (Z * (incM F d.b.1.toCols₁)ᵀ) Φ) X = d.B.ψ (d.tt (d.gram Z X)) * d.T Φ X
end PositivityTheory.SiegelWeilFormula
end
end
