module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
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

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH IsDedekindDomain NumberField Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev

noncomputable section

namespace GlobalTheory.FrameBlockDiagonal

theorem rankV (D : D7) (k : Fin D.R.m) : (Vc D k).rank = D.R.nV := by
  rw [D.sp.V_rank _ (Nat.le_add_left _ _) k.2]

def IsBlockDiagonalWithIdentity {K : Type} [CommRing K] {n r : ℕ} (x : GL (Fin r) K) (y : GL (Fin n) K) : Prop :=
  ∀ a b : Fin n, y.val a b =
    if h : a.val < r ∧ b.val < r then x.val ⟨a.val, h.1⟩ ⟨b.val, h.2⟩ else if a = b then 1 else 0

end GlobalTheory.FrameBlockDiagonal

end
