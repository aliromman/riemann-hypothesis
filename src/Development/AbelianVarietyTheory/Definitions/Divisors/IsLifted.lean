module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsEulerContraction
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

namespace GlobalTheory.DI

def IsLifted (p : ℕ) {X : Scheme.{0}} [IsIntegral X] (Z : Set X) {ι : Type} (U : ι → X.Opens) {n : ℕ}
    (x : ι → Fin n → X.functionFieldˣ) : Prop :=
  ∃ (Kt : Type) (_ : CommRing Kt) (π : Kt →+* X.functionField) (F : ι → Kt →+* Kt),
    IsFlatLift p π ∧ (∀ i, IsFrob p π (F i)) ∧
    (∀ i l, ∃ z, π z = (x i l : X.functionField) ∧ F i z = z ^ p) ∧
    ∀ (y : X) (s : Finset ι), (∀ i ∈ s, y ∈ U i) → ∀ g : X.functionFieldˣ, LogDR.LogUnit Z y g →
      LogLift p π F s (LogDR.locRing y : Set X.functionField) (g : X.functionField)

def stalkIm {Y : Scheme.{0}} {η y : Y} (h : η ⤳ y) : Subring (Y.presheaf.stalk η) :=
  (Y.presheaf.stalkSpecializes h).hom.range

end GlobalTheory.DI
