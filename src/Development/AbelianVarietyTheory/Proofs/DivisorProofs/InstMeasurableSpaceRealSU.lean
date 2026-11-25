module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
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
namespace GlobalTheory.SUVol
open NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

instance instMeasurableSpaceRealSU (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) :
    MeasurableSpace (realSU Ψ G) := borel _
instance instBorelSpaceRealSU (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) :
    BorelSpace (realSU Ψ G) := ⟨rfl⟩
end GlobalTheory.SUVol
end
