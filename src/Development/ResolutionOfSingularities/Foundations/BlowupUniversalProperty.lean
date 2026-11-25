module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.Combinatorics.Quiver.ReflQuiver
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

section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.Blowup

def IsLocallyGeneratedByNonZeroDivisor {X : Scheme.{u}} (I : X.IdealSheafData) : Prop :=
  ∀ x : X, ∃ (U : X.affineOpens) (f : Γ(X, U.1)),
    x ∈ U.1 ∧ f ∈ nonZeroDivisors Γ(X, U.1) ∧ I.ideal U = Ideal.span {f}

def IsBlowupAlongIdealSheaf {X X' : Scheme.{u}} (π : X' ⟶ X) (I : X.IdealSheafData) : Prop :=
  IsLocallyGeneratedByNonZeroDivisor (I.comap π) ∧
    ∀ (W : Scheme.{u}) (g : W ⟶ X), IsLocallyGeneratedByNonZeroDivisor (I.comap g) →
      ∃! h : W ⟶ X', h ≫ π = g

end FunctorialResolution.Blowup

end

end
