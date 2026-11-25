module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairHermitianFormInvertibleSimilitude
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

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.similitudePair_hermitianForm_invertible_similitude : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (v : InfinitePlace G.F), (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)).IsHermitian ∧ (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)).det ≠ 0 ∧ (G.psi v P.γ)ᴴ * (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) * G.psi v P.γ = ((P.c : ℚ) : ℂ) • (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) := by
  first | (exact @GlobalTheory.LKMid.pair_form_laws)
