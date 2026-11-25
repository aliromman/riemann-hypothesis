module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
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

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace

namespace GlobalTheory.CompanionTheory.WaveK.Base

open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveK
open PositivityTheory.RgTw (Mat G)

open scoped Matrix.Norms.Elementwise

variable {n : ℕ}

def RwLin : Prop :=
  ∀ (n : ℕ) (V W : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    (ι : Type) [Fintype ι] (L : ι → V →L[ℝ] W) (f : ι → Mat n → V), (∀ i, ContDiffOn ℝ ∞ (f i) (GLs n)) →
    ∀ (w : List (Bool × Fin n × Fin n)), ∀ x ∈ GLs n, Rw w (fun y => ∑ i, L i (f i y)) x = ∑ i, L i (Rw w (f i) x)

end GlobalTheory.CompanionTheory.WaveK.Base
