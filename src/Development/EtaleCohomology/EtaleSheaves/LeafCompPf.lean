module

public import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField
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
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.E4

def LeafCoprod : Prop := Hyps → ∀ (q : ℕ) (n i : ℤ) (m : ℕ) (Z : Fin m → Scheme.{0}),
  (∀ j, Finite (Ht q (sch.obj (Z j)) n i)) → Finite (Ht q (sch.obj (∐ Z)) n i)

def LeafCompGeom : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} (p : X ⟶ Sp k) [IsProper p],
  ∃ (m : ℕ) (Z : Fin m → Scheme.{0}) (ι : ∀ j, Z j ⟶ X), (∀ j, IsClosedImmersion (ι j) ∧ IsIntegral (Z j)) ∧
    IsProper (Sigma.desc ι) ∧ Surjective (Sigma.desc ι)

theorem LeafComp_of (hC : LeafCoprod) (hG : LeafCompGeom) : LeafComp := by
  intro hH q k _ X p _ n i hZ
  obtain ⟨m, Z, ι, hι, hP, hS⟩ := hG k p
  exact ⟨∐ Z, Sigma.desc ι, hP, hS, hC hH q n i m Z (fun j => hZ (Z j) (ι j) (hι j).1 (hι j).2)⟩

end LateralTheory.E.E4
