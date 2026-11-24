module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
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

open scoped MatrixGroups

namespace GlobalTheory.K4

open GlobalTheory.KZ

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def lev (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) : Subfield X.K :=
  ⨅ γ ∈ Γ', RingHom.eqLocusField (X.sl (ofSL γ)).toRingEquiv.toRingHom (RingHom.id X.K)

def mdl (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (S : Subgroup (Ω ≃ₐ[ℚ] Ω)) : Subfield X.K :=
  lev X Γ' ⊓ ⨅ s ∈ S, RingHom.eqLocusField (X.gal s).toRingHom (RingHom.id X.K)

end GlobalTheory.K4
