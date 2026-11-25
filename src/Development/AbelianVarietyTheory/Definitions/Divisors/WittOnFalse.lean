module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
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

open CategoryTheory

namespace GlobalTheory

namespace PDivGroup

open PDiv

variable {p : ℕ} {k : Type} [CommRing k]

def IsConn (G : PDivGroup p k) : Prop := ∀ n, ∀ a ∈ augIdeal k (G.A n), IsNilpotent a

def IsEt (G : PDivGroup p k) : Prop := ∀ n, IsReduced (G.A n)

end PDivGroup

end GlobalTheory
