module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NonFieldTypeVanishing
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LinearIndependentE
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

open MeasureTheory Set Filter NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.Chamber GlobalTheory.AdelicU GlobalTheory.TruncKer GlobalTheory.Orb

noncomputable section

namespace MainStatements.RegularCuspidalTrace

def IsCuspFn {D : D7} {V : HSp D} (f : GA D V → ℂ) : Prop :=
  ∀ 𝔉 : IsoFlag V, 𝔉.Proper → GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing.UnipIntegralsVanish 𝔉 f

def RegClassInt : Prop :=
  ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] (f : GA D V → ℂ), f ∈ CcGA V → IsCuspFn f →
    ∀ γ : GF V, IsRegSS γ.1.1 →
      Integrable (descend (GQ V) (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (GQ V) (rat V γ) f)) (autMeasure V μ)

def RegClassFin : Prop :=
  ∀ (D : D7) (V : HSp D) (f : GA D V → ℂ), f ∈ CcGA V →
    {𝔬 : Set (GF V) | (∃ γ : GF V, IsRegSS γ.1.1 ∧ 𝔬 = {δ | IsConj γ δ}) ∧
      ∃ (x : GA D V) (δ : GF V), δ ∈ 𝔬 ∧ f (x⁻¹ * rat V δ * x) ≠ 0}.Finite

end MainStatements.RegularCuspidalTrace

end
