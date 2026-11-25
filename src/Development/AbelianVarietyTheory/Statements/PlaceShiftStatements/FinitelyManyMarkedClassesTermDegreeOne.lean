module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
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

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid
open scoped TensorProduct Classical

namespace GlobalTheory.RootSumWeights

def FinitelyManyMarkedClassesTermDegreeOne : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ (L : G.Level) (f : G.GAf → ℂ) (K' : Subgroup (Gr G 1))
    (f' : Gr G 1 → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
    IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
    {q : Cls G | (∃ μ, (Quot.out q).Mark μ) ∧ (Quot.out q).term L.K.toSubgroup f 1 K' f' ≠ 0}.Finite

end GlobalTheory.RootSumWeights
