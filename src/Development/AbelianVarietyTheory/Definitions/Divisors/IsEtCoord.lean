module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Mathlib.RingTheory.RingHom.Etale
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LogPair

variable {R : Type} [CommRing R] {X : Scheme.{0}}

def cstOn (p : X ⟶ Sp R) (U : X.Opens) : R →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appLE ⊤ U le_top).hom

def IsEtCoord (p : X ⟶ Sp R) (U : X.Opens) {d : ℕ} (t : Fin d → Γ(X, U)) : Prop :=
  (MvPolynomial.eval₂Hom (cstOn p U) t).Etale

structure SncChart (p : X ⟶ Sp R) (d : ℕ) {s : ℕ} (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) where

  U : X.Opens
  affine : IsAffineOpen U

  t : Fin d → Γ(X, U)
  etale : IsEtCoord p U t

  c : ∀ i, (L i).ι
  le : ∀ i, U ≤ (L i).U (c i)

  e : Fin s → Option (Fin d)
  inj : ∀ i j a, e i = some a → e j = some a → i = j

  u : Fin s → Γ(X, U)ˣ
  eq : ∀ i, resG X (le i) ((σ i).f (c i)) = (u i : Γ(X, U)) * (e i).elim 1 t

structure RelSnc (p : X ⟶ Sp R) (d : ℕ) {s : ℕ} (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) : Prop where
  isLB : ∀ i, (L i).IsLB
  chart : ∀ x : X, ∃ C : SncChart p d L σ, x ∈ C.U

end GlobalTheory.LogPair
