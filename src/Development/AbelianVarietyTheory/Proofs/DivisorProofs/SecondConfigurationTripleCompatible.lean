module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFinprodSchwartzBruhatFiniteAdel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFiniteAdelesMemSpanRestrictedProdu
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsClmThetaSumRhoPure
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ConeMeasV

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

end GlobalTheory.ConeMeasV

namespace GlobalTheory.ConeMeasV

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def schrLin {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (w : (κ → AF F) × (κ → AF F)) :
    ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) where
  toFun Φ := schr ψ w Φ
  map_add' Φ Ψ := by funext x; simp [schr, mul_add]
  map_smul' c Φ := by funext x; simp [schr]; ring

theorem schrLin_apply {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (w : (κ → AF F) × (κ → AF F))
    (Φ : (κ → AF F) → ℂ) : schrLin ψ w Φ = schr ψ w Φ := rfl

theorem schr_mem_schA {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (w : (κ → AF F) × (κ → AF F))
    {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : schr ψ w Φ ∈ schA F κ := by
  have : schA F κ ≤ (schA F κ).comap (schrLin ψ w) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, g, hg, rfl⟩
    obtain ⟨T, g', hg', hT⟩ := GlobalTheory.ThetaHeisCLM.exists_schr_pureA_eq ψ hψ w hg
    show schrLin ψ w (pureA F f g) ∈ schA F κ
    rw [schrLin_apply, hT]
    exact Submodule.subset_span ⟨T f, g', hg', rfl⟩
  exact this hΦ

end GlobalTheory.ConeMeasV

namespace GlobalTheory.ConeMeasV

end GlobalTheory.ConeMeasV
