module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryIwahoriFacts
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

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical

theorem _root_.GlobalTheory.T.unitary_iwahori_facts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n : ℕ) (b : GLw n w), IsWitt n w b → (∀ g : GLw n w, b * g * b⁻¹ ∈ UL n w ↔ g ∈ UJ (cj w) (antiJ (w.adicCompletion E) n)) ∧ (∀ γ : UL n w, γ ∈ iwU n w b ↔ b⁻¹ * γ.1 * b ∈ iwGL n w) ∧ IsCompact (iwU n w b : Set (UL n w)) ∧ ∀ u : Fin n → (w.adicCompletion E)ˣ, GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u ∈ UJ (cj w) (antiJ (w.adicCompletion E) n) ↔ ∀ i, cj w (u i) * u (Fin.rev i) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.UnitaryWitt.unitary_hyperbolic_basis
