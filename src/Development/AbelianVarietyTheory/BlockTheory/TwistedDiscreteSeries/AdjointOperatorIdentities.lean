module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HasConductorMulShift
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

open ValuativeRel Matrix IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.AdjointOperatorIdentities

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in
structure Vanishing (n : Type) [Fintype n] [DecidableEq n] (M : Type) [AddCommGroup M] [Module ℂ M] (ϖ : Unif k) :
    Prop where

  invariant_eq_zero : ∀ (π : Representation ℂ (GL n k) M) (P : Pair k n) (v : levelVec π P),
    formOf π P v ∈ Mram k n M → ∀ (M' : Type) [AddCommGroup M'] [Module ℂ M'] (θ : M →ₗ[ℂ] M'),
    ((∀ g ∈ latStab P.lat, ∀ w, θ (π g w) = θ w) ∨ (∀ g ∈ latStab P.ker, ∀ w, θ (π g w) = θ w)) → θ v = 0


variable (k) in
structure OperatorIdentities (n : Type) [Fintype n] (M : Type) [AddCommGroup M] [Module ℂ M] (ϖ : Unif k)
    (χ : AddChar 𝓀[k] ℂ) : Prop where

  FFStar_FF_ram : ∀ φ ∈ Mram k n M, FFStar ϖ χ (FF ϖ χ φ) = ((resCard k : ℂ) ^ Fintype.card n) • φ

  FF_FFStar_ram : ∀ φ ∈ Mram k n M, FF ϖ χ (FFStar ϖ χ φ) = ((resCard k : ℂ) ^ Fintype.card n) • φ

  FF_mem_ram : ∀ φ ∈ Mram k n M, FF ϖ χ φ ∈ Mram k n M

  FFStar_mem_ram : ∀ φ ∈ Mram k n M, FFStar ϖ χ φ ∈ Mram k n M

  dia_mem_ram : ∀ c : 𝓀[k]ˣ, ∀ φ ∈ Mram k n M, dia c φ ∈ Mram k n M


variable (k) in
structure AdjointIdentities (n : Type) [Fintype n] (ϖ : Unif k) (χ : AddChar 𝓀[k] ℂ) : Prop where

def PairOperatorStatement : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ϖ : Unif k) (ψ : AddChar k Circle) (hψ : HasConductor ψ 1) (n : Type) [Fintype n] [DecidableEq n],
    (∀ (M : Type) [AddCommGroup M] [Module ℂ M],
      Vanishing k n M ϖ ∧ OperatorIdentities k n M ϖ (resChar ψ hψ ϖ)) ∧
    AdjointIdentities k n ϖ (resChar ψ hψ ϖ)

section Examples

end Examples

end GlobalTheory.IndefiniteRowSideFullHecke.AdjointOperatorIdentities
