module

public import Formalism.PadicSubsetSums.CentralIdempotents.IsConstituent
public import Mathlib.LinearAlgebra.Matrix.Permutation
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

namespace ReciprocityTheory.Ty.Fin

section Gen

variable {Γ : Type} [Group Γ]

def IsIrr {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V) : Prop :=
  Nontrivial V ∧ ∀ W : Submodule ℂ V, (∀ g, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = ⊤

def zIdem [Fintype Γ] (τ : FDRep ℂ Γ) : MonoidAlgebra ℂ Γ :=
  ∑ γ : Γ, MonoidAlgebra.single γ
    ((Module.finrank ℂ τ : ℂ) / Fintype.card Γ * LinearMap.trace ℂ τ (τ.ρ γ⁻¹))

def centralIdem [Fintype Γ] {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V) :
    MonoidAlgebra ℂ Γ :=
  ∑ γ : Γ, MonoidAlgebra.single γ
    ((Module.finrank ℂ V : ℂ) / Fintype.card Γ * LinearMap.trace ℂ V (ρ γ⁻¹))

theorem zIdem_eq_centralIdem [Fintype Γ] (τ : FDRep ℂ Γ) : zIdem τ = centralIdem τ.ρ := rfl



end Gen

section GeneralLinearIntegers

variable (K : Type) [Field K] [Fintype K] [DecidableEq K]

abbrev IsCuspidal {ι : Type} [Fintype ι] [DecidableEq ι] (τ : FDRep ℂ (GL ι K)) : Prop :=
  Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal K τ



variable {K}



variable (K) in
def pm {ι : Type} [Fintype ι] [DecidableEq ι] (σ : Equiv.Perm ι) : GL ι K :=
  (Matrix.permMatrixHom (n := ι) (R := K)).toHomUnits σ

end GeneralLinearIntegers

namespace Lq

end Lq

end ReciprocityTheory.Ty.Fin
