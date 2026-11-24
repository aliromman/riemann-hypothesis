module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingEquivTransportsVarietyPairData
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

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.ringEquiv_transports_varietyPair_data : ∀ {k K K' : Type} [Field k] [CharZero k] [Field K] [Field K'] (c : k →+* K) (c' : k →+* K') (e : K ≃+* K'),
  (∀ a, e (c a) = c' a) → ∀ (n : ℕ) (x : Fin n → K) (R : Subring K) (φ : K →₀ ℚ), TrBasis c x →
  TrBasis c' (e ∘ x) ∧
  (IsLocModel c R ↔ IsLocModel c' (R.map e.toRingHom)) ∧
  (Klt c n R (dForm c x) φ ↔ Klt c' n (R.map e.toRingHom) (dForm c' (e ∘ x)) (Finsupp.mapDomain e φ)) ∧
  (EffAt c n R (dForm c x) φ ↔ EffAt c' n (R.map e.toRingHom) (dForm c' (e ∘ x)) (Finsupp.mapDomain e φ)) := by
  first | exact @GlobalTheory.FieldPair.transport_ringEquiv
