module

public import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.TotallySplit
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

namespace GlobalTheory.EtC

def IsExcisionNbhd (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A) : Prop :=
  Algebra.Etale A A' ∧ (∀ a' : A', ∃ a : A, a' - algebraMap A A' a ∈ Ideal.span {algebraMap A A' f}) ∧
    ∀ a : A, algebraMap A A' a ∈ Ideal.span {algebraMap A A' f} → a ∈ Ideal.span {f}

theorem isExcisionNbhd_self (A : Type) [CommRing A] (f : A) : IsExcisionNbhd A A f :=
  ⟨inferInstance, fun a' => ⟨a', by simp⟩, fun a h => by simpa using h⟩

end GlobalTheory.EtC
