module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsRingEquivOfIsTranscendenceBasis
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

namespace GlobalTheory.CompRat

theorem exists_ringEquiv_complex_comp_eq :
    ∀ (k : Type) [Field k] [Countable k] (φ ψ : k →+* ℂ), ∃ τ : ℂ ≃+* ℂ, ∀ x, τ (φ x) = ψ x :=
  fun _ _ _ φ ψ => GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq φ ψ

end GlobalTheory.CompRat
