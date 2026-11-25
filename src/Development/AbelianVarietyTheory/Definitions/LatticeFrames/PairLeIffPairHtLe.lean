module

public import Formalism.LocalRingCardinality.DataArith
import Mathlib.Algebra.Order.Star.Real
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

namespace GlobalTheory.Core.Ht2

open NumberField Formalism.BasicNotions

section Generic

variable {K : Type} [Field K] [NumberField K] [StarRing K]

abbrev nrm (A : HLat K) (v : InfinitePlace K) (x : A.V) : ℝ := Formalism.HermitianLatticesTheory.normAt A.b A.X v x

def IsoAll (N A : HLat K) (e : N.V →ₗ[K] A.V) : Prop := ∀ v x, nrm A v (e x) = nrm N v x

def Norming (B M : HLat K) (pr : B.V →ₗ[K] Module.Dual K M.V) : Prop :=
  ∀ (w : B.V) (v : InfinitePlace K), ∃ z, v (pr w z) = nrm B v w ^ 2 ∧ nrm M v z = nrm B v w

def Reads (N B A M : HLat K) (Ψ : N.V →ₗ[K] B.V) (Φ : A.V →ₗ[K] Module.Dual K M.V) : Prop :=
  ∃ (e : N.V →ₗ[K] A.V) (pr : B.V →ₗ[K] Module.Dual K M.V),
    IsoAll N A e ∧ Norming B M pr ∧ ∀ x, Φ (e x) = pr (Ψ x)

end Generic

namespace Std

variable (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ)

variable {K n}

end Std

end GlobalTheory.Core.Ht2

end
