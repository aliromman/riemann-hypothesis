module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOnFderivApply
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryMemGLs
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

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate

namespace GlobalTheory.CompanionTheory.RCalc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

open scoped Matrix.Norms.Elementwise

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem rcalc : RCalc := by
  intro n
  refine ⟨?_, ?_, ?_⟩
  · intro V _ _ f hf
    exact ⟨fun X => Rd_contDiffOn X hf, fun X Y g hg => Rd_bracket X Y hf hg, fun s m X g hg => Rd_gel X s m hf hg,
      fun s m x hx g hg => ⟨gel_left s m hx hf hg, gel_right s m hx hf hg⟩⟩
  · intro E f hf s m
    exact gel_mem_CE E hf s m
  · intro _ _ μ _ V _ _ _ f hf hc X
    exact ibp n μ V f hf hc X

end GlobalTheory.CompanionTheory.RCalc
