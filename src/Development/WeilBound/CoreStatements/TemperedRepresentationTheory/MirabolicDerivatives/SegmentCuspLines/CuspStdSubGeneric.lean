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

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil

namespace GlobalTheory.BZSeg

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def StdSubGeneric : Prop :=
  ∀ (h N : ℕ) (Δ : Fin h → Segment k) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), (∀ i, IsLSeg (Δ i) (x i).rep) →
    (∀ i j, i < j → ¬ (Δ i).Precedes (Δ j)) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GL (Fin N) k) W) (f : σ.IntertwiningMap (prodIrr x hd)), Function.Injective f → Nontrivial W →
    IsGeneric σ

def WhitRankStd : Prop :=
  ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (h N : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N),
    Module.rank ℂ (TwJacquet (prodIrr x hd) (unipB k (Fin N)) (whitChar ψ N)) ≤ 1

end GlobalTheory.BZSeg

end
