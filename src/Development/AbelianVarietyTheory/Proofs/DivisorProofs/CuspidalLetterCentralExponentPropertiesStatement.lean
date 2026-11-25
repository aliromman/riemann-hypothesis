module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableAutomorphicSpace
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalLetterCentralExponentProperties
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

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct

theorem _root_.GlobalTheory.T.cuspidalLetter_centralExponent_properties : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (x : Letter E), (∀ φ ∈ x.2.V, zc E x.1 φ = cex x • φ) ∧ (∀ t : ℝ, cex (tw x t) = cex x + x.1 * (Module.finrank ℚ E : ℂ) * t) ∧ (1 ≤ x.1 → ∀ t : ℝ, rexp (tw x t) = rexp x + t) ∧ (cex x = 0 ↔ IsNormalised x.2) ∧ ∀ c : ℂ, (∃ φ ∈ x.2.V, φ ≠ 0 ∧ zc E x.1 φ = c • φ) → cex x = c := by
  first | exact @GlobalTheory.ResW.letter_centralExponent
