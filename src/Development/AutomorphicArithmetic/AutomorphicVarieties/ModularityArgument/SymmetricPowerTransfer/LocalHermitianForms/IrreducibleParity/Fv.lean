module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.NormOneIsCoboundaryUnramifiedQuadratic
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

namespace UpperTheory.V.Z.Sym.Loc.PS

open QuadraticAlgebra

variable (O : Type) [CommRing O] {K : Type} [Field K] [Algebra O K] (τ : K)

def Gen (S : Set (Etau K τ)) (y : (Etau K τ)ˣ) : Prop :=
  (y : Etau K τ) ∈ S ∧ ∀ w ∈ S, IsIntegral O (((y⁻¹ : (Etau K τ)ˣ) : Etau K τ) * w)

def Gs (t : K) (a : (Etau K τ)ˣ) : Set (Set (Etau K τ)) :=
  {S | IsFixP O τ t S ∧ ∃ c ∈ Cint O τ, Gen O τ S (a * c)}

def Fv : Set (Set (Set (Etau K τ))) :=
  {X | ∃ S, IsLat O τ S ∧ (∀ y ∈ S, ω * y ∈ S) ∧ (∃ c ∈ Cint O τ, Gen O τ S c) ∧ X = cls τ S}

end UpperTheory.V.Z.Sym.Loc.PS
