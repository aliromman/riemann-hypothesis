module

public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn
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

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib

namespace GlobalTheory.RgGu.Leib

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def PhiPG0 : Prop :=
  ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (t : ℕ) (τ : MRep k 0) (σ : GRep k (t + 1)), IsSmooth σ.ρ →
      MIso (phiN ψ (mcast (by omega : 0 + (t + 1) = (0 + t) + 1) (prodPGn τ σ))) (prodGPn (psiN τ) (gres σ))

end GlobalTheory.RgGu.Leib

end
