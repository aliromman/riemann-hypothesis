module

public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsSmoothAutomorphicFunctionCompactFamilyAverage
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory Matrix
open scoped TensorProduct

theorem _root_.GlobalTheory.T.isSmoothAutomorphicFunction_compactFamily_average : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam (D := D) θ → ∀ (V : HSp D) (τ : D.what₂.Tau) (K : Type) [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] (κ : K → Matrix (Fin V.rank) (Fin V.rank) ℂ), Continuous κ → (∀ k, κ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) → ∀ e : K → ℂ, Continuous e → ∀ φ : GA D V → ℂ, IsAutFunSm θ V φ → IsAutFunSm θ V (fun x => ∫ k, e k * φ (x * atTau θ V τ (κ k)) ∂μ) := by
  first | exact @GlobalTheory.RealAverage.isAutFunSm_average
