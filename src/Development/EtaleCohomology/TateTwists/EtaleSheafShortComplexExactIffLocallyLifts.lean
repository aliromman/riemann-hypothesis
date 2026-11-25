module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
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

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleSheafShortComplexExactIffLocallyLifts : Prop :=
  ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R)), S.Exact ↔ ∀ U (b : Sec S.X₂ U), Sec.map S.g b = 0 → Loc U fun V g => ∃ a : Sec S.X₁ V, Sec.map S.f a = Sec.res g b
