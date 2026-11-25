module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerAlong
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTermLinearThetaFunctions
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
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm

theorem _root_.GlobalTheory.T.mixedModelTerm_linear_thetaFunctions : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ y : Matrix (Fin W.rank) (Fin r) D.host.E, (∀ G H : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W H → term ψ V V' W C C' B μ 𝓨 (G + H) y = term ψ V V' W C C' B μ 𝓨 G y + term ψ V V' W C C' B μ 𝓨 H y) ∧ ∀ (c : ℂ) (G : WO V W → ℂ), IsThetaFunO ψ V W G → term ψ V V' W C C' B μ 𝓨 (c • G) y = c * term ψ V V' W C C' B μ 𝓨 G y := by
  first | exact @GlobalTheory.MixedTerm.term_linear
