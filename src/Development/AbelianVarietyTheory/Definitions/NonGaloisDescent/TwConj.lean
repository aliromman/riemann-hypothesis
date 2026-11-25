module

public import Mathlib.FieldTheory.Separable
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

open Matrix

noncomputable section

namespace GlobalTheory.Tw

variable {n : ℕ} {R : Type} [CommRing R] [StarRing R]

def Phi (n : ℕ) (R : Type) [CommRing R] : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if (i : ℕ) + (j : ℕ) + 1 = n then (-1) ^ (i : ℕ) else 0

def theta (g : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R := Phi n R * (g⁻¹)ᴴ * (Phi n R)ᵀ

def nrm (δ : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R := δ * theta δ

def twConj (x δ : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R := x⁻¹ * δ * theta x

def Reg (δ : Matrix (Fin n) (Fin n) R) : Prop := IsUnit δ ∧ (nrm δ).charpoly.Separable

def cent (δ : Matrix (Fin n) (Fin n) R) : Set (Matrix (Fin n) (Fin n) R) := {g | IsUnit g ∧ g * δ = δ * theta g}

def adj (δ g : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R := δ * Phi n R * gᴴ * (Phi n R)ᵀ * δ⁻¹

end GlobalTheory.Tw
