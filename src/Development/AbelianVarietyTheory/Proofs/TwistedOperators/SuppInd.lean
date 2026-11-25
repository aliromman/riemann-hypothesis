module

public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
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

open Classical

namespace GlobalTheory.LevelVecNorm

def locH {E : Type} [Field E] [NumberField E] (Pg : Finset (Formalism.L2.DIV.Pl E)) {r : ℕ}
    (Hl : ∀ PP : ↥Pg, Subgroup (GL (Fin r) (Formalism.L2.DIV.kP PP.1))) (PP : Formalism.L2.DIV.Pl E) :
    Subgroup (GL (Fin r) (Formalism.L2.DIV.kP PP)) :=
  if h : PP ∈ Pg then Hl ⟨PP, h⟩ else ⊤


open Classical in
def suppInd {k : Type} [CommRing k] (r : ℕ) {b a : ℕ} (H : Subgroup (GL (Fin r) k)) (z : Matrix (Fin b) (Fin a) k) : ℝ :=
  if Formalism.IndefR.Datum.LowZero r z ∧ ∃ g ∈ H, ((g : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) = Formalism.IndefR.Datum.topL r z then 1 else 0

end GlobalTheory.LevelVecNorm

end
