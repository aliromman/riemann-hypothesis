module

public import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
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

open Coalgebra Bialgebra

namespace GlobalTheory.PDiv

def frobKerIdeal (p : ℕ) (R H : Type) [CommRing R] [CommRing H] [Bialgebra R H] : Ideal H :=
  Ideal.span ((fun a : H => a ^ p) '' (augIdeal R H : Set H))

theorem pow_mem_frobKerIdeal {p : ℕ} {R H : Type} [CommRing R] [CommRing H] [Bialgebra R H] {a : H}
    (ha : a ∈ augIdeal R H) : a ^ p ∈ frobKerIdeal p R H :=
  Ideal.subset_span ⟨a, ha, rfl⟩

theorem frobKerIdeal_le_augIdeal {p : ℕ} (hp : p ≠ 0) (R H : Type) [CommRing R] [CommRing H]
    [Bialgebra R H] : frobKerIdeal p R H ≤ augIdeal R H :=
  Ideal.span_le.2 fun _ ⟨a, ha, e⟩ => e ▸ Ideal.pow_mem_of_mem _ ha p (Nat.pos_of_ne_zero hp)

end GlobalTheory.PDiv
