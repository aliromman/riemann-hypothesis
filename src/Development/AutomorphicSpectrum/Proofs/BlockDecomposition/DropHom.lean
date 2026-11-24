module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
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

open GlobalTheory.SmGL

namespace GlobalTheory.CompanionTheory.FineProd

variable {k : Type} [Field k]

def dropHom {r r' : ℕ} (d : Fin r → ℕ) (o : Fin r' → Fin r) :
    Levi k (fun j => Fin (d j)) →* Levi k (fun a => Fin (d (o a))) where
  toFun g a := g (o a)
  map_one' := rfl
  map_mul' _ _ := rfl

end GlobalTheory.CompanionTheory.FineProd

end
