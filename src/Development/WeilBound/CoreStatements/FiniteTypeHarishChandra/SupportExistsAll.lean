module

public import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.FiniteDimensionalHcSpace
public import Mathlib.RepresentationTheory.Character
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

open Polynomial CategoryTheory
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal

noncomputable section

namespace ReciprocityTheory.Ty.Fin.St

def SimpleIffIrr : Prop :=
  (∀ (Γ : Type) [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ), Simple τ ↔ IsIrr τ.ρ) ∧
  ∀ (Γ : Type) [Group Γ] [Fintype Γ] (τ σ : FDRep ℂ Γ), Nonempty (τ ≅ σ) ↔ ∃ e : τ ≃ₗ[ℂ] σ, ∀ γ v, e (τ.ρ γ v) = σ.ρ γ (e v)

end ReciprocityTheory.Ty.Fin.St
