module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
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

open NumberField GlobalTheory.CuspRep

namespace GlobalTheory.CompanionTheory.CTFin

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

def capR (r s : ℕ) (τ : E →+* ℂ) (u : ℂ) : Module.End ℂ (Sm E (r + s)) :=
  Formalism.REAL.qdet (fun i j : Fin r => Eop (a := r + s) τ (Fin.castAdd s i) (Fin.castAdd s j)) (u + ((r : ℂ) - 1) / 2)

def capS (r s : ℕ) (τ : E →+* ℂ) (u : ℂ) : Module.End ℂ (Sm E (r + s)) :=
  Formalism.REAL.qdet (fun i j : Fin s => Eop (a := r + s) τ (Fin.natAdd r i) (Fin.natAdd r j)) (u + ((s : ℂ) - 1) / 2)

end GlobalTheory.CompanionTheory.CTFin

end
