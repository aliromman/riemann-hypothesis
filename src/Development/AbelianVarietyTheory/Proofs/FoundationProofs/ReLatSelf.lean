module

public import Formalism.LocalRingCardinality.DataSpaces
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

namespace GlobalTheory.VolRatioCompare

open NumberField Formalism.BasicNotions

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def reLat (V : HSpace E) (L : Submodule (𝓞 E) V.V) (h1 : Submodule.IsLattice E L)
    (h2 : Formalism.HermitianLatticesTheory.IsUnimodular V.hT L) : HSpace E :=
  { V with L0 := L, standardTuple_isLattice := h1, baseLattice_isUnimodular := h2 }

end GlobalTheory.VolRatioCompare
