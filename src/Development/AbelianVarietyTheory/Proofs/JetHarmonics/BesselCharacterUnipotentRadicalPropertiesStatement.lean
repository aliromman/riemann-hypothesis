module

public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselCharacterUnipotentRadicalProperties
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

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.besselCharacter_unipotentRadical_properties : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ), Formalism.QuantumDeterminants.inWb k r z → (∀ g, ‖Formalism.QuantumDeterminants.psi k r z c g‖ = 1) ∧ (∀ m ∈ Formalism.QuantumDeterminants.Nset k r, ∀ m' ∈ Formalism.QuantumDeterminants.Nset k r, m * m' ∈ Formalism.QuantumDeterminants.Nset k r ∧ Formalism.QuantumDeterminants.psi k r z c (m * m') = Formalism.QuantumDeterminants.psi k r z c m * Formalism.QuantumDeterminants.psi k r z c m') ∧ (∀ m ∈ Formalism.QuantumDeterminants.Nset k r, m⁻¹ ∈ Formalism.QuantumDeterminants.Nset k r ∧ Formalism.QuantumDeterminants.psi k r z c m⁻¹ = star (Formalism.QuantumDeterminants.psi k r z c m)) ∧ (∀ g ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ m ∈ Formalism.QuantumDeterminants.Nset k r, g * m * g⁻¹ ∈ Formalism.QuantumDeterminants.Nset k r ∧ g⁻¹ * m * g ∈ Formalism.QuantumDeterminants.Nset k r ∧ Formalism.QuantumDeterminants.psi k r z c (g * m * g⁻¹) = Formalism.QuantumDeterminants.psi k r z c m ∧ Formalism.QuantumDeterminants.psi k r z c (g⁻¹ * m * g) = Formalism.QuantumDeterminants.psi k r z c m) ∧ (∀ g ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ g' ∈ Formalism.QuantumDeterminants.UWset k r z, g * g' ∈ Formalism.QuantumDeterminants.UWset k r z ∧ g⁻¹ ∈ Formalism.QuantumDeterminants.UWset k r z ∧ g ∈ GG k r) ∧ ∀ m ∈ Formalism.QuantumDeterminants.Nset k r, m ∈ GG k r := by
  first | exact @GlobalTheory.BesselPsi.psi_character
