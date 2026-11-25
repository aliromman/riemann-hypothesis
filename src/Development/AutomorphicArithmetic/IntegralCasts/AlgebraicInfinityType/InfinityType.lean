module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
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
import Mathlib.Tactic.TypeStar

@[expose] public section

namespace Reformulated.AlgebraicInfinityType

open NumberField

@[ext]
structure InfinityType (F : Type*) [Field F] (n : ℕ) where

  pairs : (F →+* ℂ) → Multiset (ℂ × ℂ)
  card_pairs : ∀ σ, Multiset.card (pairs σ) = n
  sub_int : ∀ σ, ∀ p ∈ pairs σ, ∃ m : ℤ, p.1 - p.2 = m
  pairs_conjugate : ∀ σ, pairs (ComplexEmbedding.conjugate σ) = (pairs σ).map Prod.swap

namespace InfinityType

variable {F : Type*} [Field F] {n : ℕ}

def exponents (t : InfinityType F n) (σ : F →+* ℂ) : Multiset ℂ :=
  (t.pairs σ).map Prod.fst

def IsAlgebraic (t : InfinityType F n) : Prop :=
  ∀ σ, ∀ a ∈ t.exponents σ, ∃ m : ℤ, a = ((n : ℂ) - 1) / 2 + m

def IsRegular (t : InfinityType F n) : Prop :=
  ∀ σ, (t.exponents σ).Nodup

def IsRegularAlgebraic (t : InfinityType F n) : Prop :=
  t.IsAlgebraic ∧ t.IsRegular

end InfinityType

end Reformulated.AlgebraicInfinityType
