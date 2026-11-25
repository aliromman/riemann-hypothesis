module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
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

noncomputable section

namespace UpperTheory.V.Z.Sym.Glob.Fib

open NumberField

def LevFin : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → D.U2 ≤ D.UZ ∧ D.U2.relIndex (D.UZ ⊓ SA Δ) ≠ 0

def DetOne : Prop :=
  ∀ (O K : Type) [CommRing O] [Field K] [Algebra O K] (Δ : K) (g : DX Δ), g ∈ ZD Δ ⊔ KD Δ O → g ∈ SU Δ → g ∈ KD Δ O

def FSConj : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∀ t, D.Cone t → ∀ u ∈ D.UZ, ∀ g, D.FS t (u⁻¹ * g * u) = D.FS t g

def FSSupp : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∀ ι, IsIotaD ι → ∀ t, D.Cone t → ∀ (γ : DX Δ) s g, HasTr γ s →
    D.FS t (g⁻¹ * ι γ * g) ≠ 0 → D.admitted t s

def HasTrLaw : Prop :=
  ∀ (K : Type) [Field K] (Δ : K) (γ : DX Δ), (γ ∈ SU Δ ↔ ∃ s, HasTr γ s) ∧ (∀ s s', HasTr γ s → HasTr γ s' → s = s') ∧
    ∀ (h : DX Δ) s, HasTr (h * γ * h⁻¹) s ↔ HasTr γ s

end UpperTheory.V.Z.Sym.Glob.Fib
