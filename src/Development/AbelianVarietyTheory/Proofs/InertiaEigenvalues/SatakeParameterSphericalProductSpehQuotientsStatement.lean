module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
public import Mathlib.Data.Multiset.Functor
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsUnitarisableTrivChar

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DefiniteBC GlobalTheory.BcSpeh

theorem _root_.GlobalTheory.T.satakeParameter_spherical_product_spehQuotients : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (c n : ℕ) (a d : Fin c → ℕ) (h : ∑ i, d i * a i = n) (ρ : ∀ i, LocIrr w (a i)) (σ : ∀ i, LocIrr w (d i * a i)), (∀ i, 1 ≤ d i) → (∀ i, GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of (ρ i).ρ (ρ i).smooth (ρ i).irred) (d i) (σ i).ρ) → ∀ T : Multiset ℂˣ, GlobalTheory.LFun.HasSatGL w (locProd h w σ) T → ∃ S : Fin c → Multiset ℂˣ, (∀ i, GlobalTheory.LFun.HasSatGL w (ρ i).ρ (S i)) ∧ ∑ i, ∑ k : Fin (d i), (S i).map (fun z => (z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((d i : ℂ) - 1) / 2 - (k : ℕ))) = T.map (fun z => (z : ℂ)) := by
  first | exact @GlobalTheory.SatInd.satake_locProd_speh
