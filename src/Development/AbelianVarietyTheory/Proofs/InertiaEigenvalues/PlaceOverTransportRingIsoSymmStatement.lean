module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIsoSymm
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

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published

theorem _root_.GlobalTheory.T.place_over_transport_ring_iso_symm : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] (A' : ValuationSubring Ω') (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A' w') (φ : Ω ≃+* Ω') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), PlaceIso A w A' w' φ j i → ∃ S : WD h ≃ WD h', (∀ y y', WDRel φ y y' ↔ S y = y') ∧ (∀ y, (S y).lpDim = y.lpDim) ∧ S (WD.lpZero (h := h)) = WD.lpZero (h := h') ∧ (∀ y z, S (y.lpSum z) = (S y).lpSum (S z)) ∧ (∀ y z, S (y.lpChar z) = (S y).lpChar (S z)) ∧ (∀ y (s : ℝ), S (y.lpTw s) = (S y).lpTw s) ∧ (∀ n, S (WD.lpSp (h := h) n) = WD.lpSp (h := h') n) ∧ (∀ y, IsIrrWD (S y) ↔ IsIrrWD y) ∧ ∀ (ξ : Weil h →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ) (ξ' : Weil h' →* ℂˣ) (hξ' : GlobalTheory.WeilDeligne.IsSmooth ξ'), (∀ σ σ', WeilRel φ σ σ' → ξ σ = ξ' σ') → S (WD.lpOfChar h ξ hξ) = WD.lpOfChar h' ξ' hξ' := by
  exact @GlobalTheory.WDTransport.exists_equiv_wd
