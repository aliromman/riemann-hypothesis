module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Derivation.Basic
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

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CrystallineSemistableComparison.Pb

variable {K R : Type} [Field K] [CommRing R] [Algebra K R] {d : ℕ}

def tpow (t : Fin d → Rˣ) (m : Fin d → ℤ) : R := ((∏ k, t k ^ m k : Rˣ) : R)

def expS (S : Finset (Fin (d + 1))) : Set (Fin d → ℤ) :=
  {m | (∀ k : Fin d, k.succ ∉ S → 0 ≤ m k) ∧ ((0 : Fin (d + 1)) ∉ S → ∑ k, m k ≤ 0)}


variable (K) in
def torusS (t : Fin d → Rˣ) (S : Finset (Fin (d + 1))) : Subalgebra K R := Algebra.adjoin K (tpow t '' expS S)

def jacS (B : Subalgebra K R) (D : Fin d → Derivation K R R) {m : ℕ} (κ : Fin m → Fin d) : AddSubgroup R :=
  AddSubgroup.closure {y | ∃ (b : B) (bs : Fin m → B), y = (b : R) * (Matrix.of fun k l => D (κ k) (bs l)).det}

end CrystallineSemistableComparison.Pb
