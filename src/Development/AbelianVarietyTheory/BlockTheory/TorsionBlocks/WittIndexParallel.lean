module

public import Formalism.LocalRingCardinality.DataTheta
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

namespace GlobalTheory.IndefiniteRowSideFullHecke.WittIndexParallel

open Formalism.BasicNotions Formalism.BasicNotions.TH

def ParallelSig {D : D7} (V : HSp D) (p q : ℕ) : Prop :=
  ∀ τ : D.host.E →+* ℂ, Formalism.UG.HasSignature (V.gram.map τ) p q

theorem parallelSig_of_sigOK {D : D7} {V : HSp D} {p q : ℕ} (h : V.SigOK) (hs : ∀ τ, V.sig τ = (p, q)) :
    ParallelSig V p q := fun τ => by
  have := h τ
  rwa [hs τ] at this

end GlobalTheory.IndefiniteRowSideFullHecke.WittIndexParallel

end
