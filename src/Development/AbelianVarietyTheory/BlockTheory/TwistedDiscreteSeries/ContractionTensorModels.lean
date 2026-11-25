module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Formalism.LocalRingCardinality.DataHost
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.RingTheory.SimpleRing.Principal
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
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

noncomputable section

open scoped InnerProductSpace TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.ContractionTensorModels

section Hilbert

variable {H₁ H₂ FF : Type}
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
  [NormedAddCommGroup FF] [InnerProductSpace ℂ FF]

def IsIsoBilin (Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF) : Prop :=
  ∀ x x' y y', ⟪Tm x y, Tm x' y'⟫_ℂ = ⟪x, x'⟫_ℂ * ⟪y, y'⟫_ℂ

def IsEquivBilin {G₁ G₂ : Type} [Group G₁] [Group G₂] (π₁ : G₁ →* (H₁ ≃ₗᵢ[ℂ] H₁)) (π₂ : G₂ →* (H₂ ≃ₗᵢ[ℂ] H₂))
    (ρ : G₁ × G₂ →* (FF ≃ₗᵢ[ℂ] FF)) (Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF) : Prop :=
  ∀ g h x y, Tm (π₁ g x) (π₂ h y) = ρ (g, h) (Tm x y)

def IsContr (Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF) (It : FF →ₗ[ℂ] H₂ →ₛₗ[starRingEnd ℂ] H₁) : Prop :=
  ∀ φ y x, ⟪x, It φ y⟫_ℂ = ⟪Tm x y, φ⟫_ℂ

end Hilbert

def ContrHilbert : Prop :=
  ∀ (H₁ H₂ FF : Type)
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    [NormedAddCommGroup FF] [InnerProductSpace ℂ FF] [CompleteSpace FF]
    (G₁ G₂ : Type) [Group G₁] [Group G₂] (π₁ : G₁ →* (H₁ ≃ₗᵢ[ℂ] H₁)) (π₂ : G₂ →* (H₂ ≃ₗᵢ[ℂ] H₂))
    (ρ : G₁ × G₂ →* (FF ≃ₗᵢ[ℂ] FF)) (Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF),
    IsIsoBilin Tm → IsEquivBilin π₁ π₂ ρ Tm →
      ∃! It : FF →ₗ[ℂ] H₂ →ₛₗ[starRingEnd ℂ] H₁, IsContr Tm It

def IsTensorIt {ι : Type} [Fintype ι] {σ : ι → Type} {Var : Type} (e : (Σ τ, σ τ) ≃ Var) {A B : ι → Type}
    [∀ τ, AddCommGroup (A τ)] [∀ τ, Module ℂ (A τ)] [∀ τ, AddCommGroup (B τ)] [∀ τ, Module ℂ (B τ)]
    (Itl : ∀ τ, MvPolynomial (σ τ) ℂ →ₗ[ℂ] A τ →ₗ[ℂ] B τ)
    (It : MvPolynomial Var ℂ →ₗ[ℂ] (⨂[ℂ] τ, A τ) →ₗ[ℂ] ⨂[ℂ] τ, B τ) : Prop :=
  ∀ (P : ∀ τ, MvPolynomial (σ τ) ℂ) (v : ∀ τ, A τ),
    It (∏ τ, MvPolynomial.rename (fun s => e ⟨τ, s⟩) (P τ)) (PiTensorProduct.tprod ℂ v) =
      PiTensorProduct.tprod ℂ fun τ => Itl τ (P τ) (v τ)

def ContrTensor : Prop :=
  ∀ (ι : Type) [Fintype ι] (σ : ι → Type) (Var : Type) (e : (Σ τ, σ τ) ≃ Var) (A B : ι → Type)
    [∀ τ, AddCommGroup (A τ)] [∀ τ, Module ℂ (A τ)] [∀ τ, AddCommGroup (B τ)] [∀ τ, Module ℂ (B τ)]
    (Itl : ∀ τ, MvPolynomial (σ τ) ℂ →ₗ[ℂ] A τ →ₗ[ℂ] B τ),
    ∃ It : MvPolynomial Var ℂ →ₗ[ℂ] (⨂[ℂ] τ, A τ) →ₗ[ℂ] ⨂[ℂ] τ, B τ,
      IsTensorIt e Itl It ∧ ((∀ τ, Itl τ ≠ 0) → It ≠ 0)

def Contraction : Prop := ContrHilbert ∧ ContrTensor

section Models

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum

end Models

end GlobalTheory.IndefiniteRowSideFullHecke.ContractionTensorModels

end
