module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
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

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace Zc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def Peel (Δ : Segment k) (x : IrrGL (k := k)) : Prop :=
  ∃ (y : Fin 2 → IrrGL (k := k)) (hd : ∑ a, (y a).1 = x.1), IsLSeg Δ (y 0).rep ∧
    ∃ f : x.rep.IntertwiningMap (prodIrr y hd), Function.Injective f




variable (k) in
def PeelGoodP : Prop :=
  ∀ (x : IrrGL (k := k)) (y : Fin 2 → IrrGL (k := k)) (hd : ∑ a, (y a).1 = x.1) (Δ : Segment k) (𝔫 : Multiset (Segment k)),
    IsLSeg Δ (y 0).rep → IsL 𝔫 (y 1).rep → (∃ f : x.rep.IntertwiningMap (prodIrr y hd), Function.Injective f) →
    (∀ Δ' ∈ 𝔫, ¬ Δ'.Precedes Δ) → IsL (𝔫 + {Δ}) x.rep

end Zc

end
