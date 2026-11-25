module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Rr

@[expose] public section

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)

open scoped Matrix.Norms.Elementwise

namespace GlobalTheory.CompanionTheory.WaveSpd

theorem isWave_time_refl : ∀ {n : ℕ} (E : KMod n) (u : ℝ → Mat n → E.V), IsWave E u → IsWave E fun s => u (-s) := by
  intro n E u hu
  obtain ⟨h1, h2, h3, h4⟩ := hu
  refine ⟨?_, fun t => h2 (-t), ?_, ?_⟩
  · have hm : Set.MapsTo (fun p : ℝ × Mat n => (-p.1, p.2)) (Set.univ ×ˢ GLs n) (Set.univ ×ˢ GLs n) :=
      fun p hp => ⟨Set.mem_univ _, hp.2⟩
    have hc : ContDiffOn ℝ ∞ (fun p : ℝ × Mat n => (-p.1, p.2)) (Set.univ ×ˢ GLs n) :=
      (contDiff_fst.neg.prodMk contDiff_snd).contDiffOn
    exact h1.comp hc hm
  · intro t g hg
    have := iteratedDeriv_comp_neg (𝕜 := ℝ) 2 (fun s => u s g) t
    rw [this, h3 (-t) g hg]
    simp
  · intro g hg
    have := deriv_comp_neg (𝕜 := ℝ) (fun s => u s g) 0
    rw [this]
    simpa using h4 g hg

end GlobalTheory.CompanionTheory.WaveSpd
