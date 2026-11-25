module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.SingToDiffAlt
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

open Matrix

namespace PositivityTheory.Rg.Sw.LVs

open scoped Matrix.Norms.Elementwise

def Equivar : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (F : Matrix ι ι ℂ → ℂ) (A : Matrix ι ι ℂ), AnalyticAt ℂ F 0 →
    detD (fun T => F (A * T)) = A.det * detD F

def Reindex : Prop :=
  ∀ (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (F : Matrix κ κ ℂ → ℂ),
    AnalyticAt ℂ F 0 → detD (fun T : Matrix ι ι ℂ => F (T.reindex e e)) = detD F

def KappaFin : Prop :=
  ∀ (N : ℕ) (t : ℤ), detD (fun T : Matrix (Fin N) (Fin N) ℂ => (1 + T).det ^ t) =
    ∏ i ∈ Finset.range N, ((t : ℂ) + i)

end PositivityTheory.Rg.Sw.LVs
