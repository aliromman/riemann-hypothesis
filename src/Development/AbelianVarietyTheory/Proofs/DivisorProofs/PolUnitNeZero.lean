module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormMulTransposeMulFormInvMem
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

namespace GlobalTheory.ZarhinFam

def polUnit (d : ℕ) : ord d :=
  ⟨single (Sum.inl 0) (Sum.inr 0) 1, fun i j => by simp [single]⟩

@[simp] theorem polUnit_coe (d : ℕ) :
    ((polUnit d : ord d) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) = single (Sum.inl 0) (Sum.inr 0) 1 :=
  rfl

end GlobalTheory.ZarhinFam
