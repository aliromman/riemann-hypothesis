module

public import Formalism.LocalRingCardinality.DataLatDefs
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

namespace GlobalTheory.IndefiniteRowSideFullHecke.IndexAtLevelRanks

open Formalism.BasicNotions Formalism.MainNotions

variable (D : D7) (u : D.what₂.Word)

def IsScaledU (w : D.what₂.places.Pl) (v : (D.mem u).A.vT)
    (g : (D.fm u).ramSub →ₗ[D.what₂.LL] (D.fm u).ramSub) : Prop :=
  ∀ x : (D.fm u).ramSub, (D.fm u).emb 0 (g x : LT.Vl D u 0) =
    (((D.mem u).A.T : ℂ) ^ (D.fm u).bTop ((D.fm u).tauOf w v)) •
      LT.Uop D u 0 v ((D.fm u).emb 0 (x : LT.Vl D u 0))

end GlobalTheory.IndefiniteRowSideFullHecke.IndexAtLevelRanks

end
