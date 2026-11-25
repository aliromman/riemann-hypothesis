module

public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.MvPowerSeries.Substitution
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

open MvPowerSeries

namespace GlobalTheory.LawDer

variable {R : Type} [CommRing R] {d : ℕ}

def atZero (H : MvPowerSeries (Fin d ⊕ Fin d) R) : MvPowerSeries (Fin d) R :=
  subst (Sum.elim (fun i => (X i : MvPowerSeries (Fin d) R)) fun _ => 0) H

def invDer (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (u : Fin d → R)
    (F : MvPowerSeries (Fin d) R) : MvPowerSeries (Fin d) R :=
  ∑ i, u i • atZero (pderiv (R := R) (Sum.inr i) (subst μ F))

end GlobalTheory.LawDer
