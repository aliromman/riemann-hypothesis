module

public import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
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

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.AnForm.R

namespace GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

def CartAt {X : Scheme.{0}} (J : X.IdealSheafData) (x : X) : Prop :=
  ∃ (U : X.affineOpens) (f : Γ(X, U.1)), x ∈ U.1 ∧ f ∈ nonZeroDivisors Γ(X, U.1) ∧ J.ideal U = Ideal.span {f}

theorem effCartier_iff_forall_cartAt {X : Scheme.{0}} (J : X.IdealSheafData) :
    FinalTheorems.EffCartier J ↔ ∀ x, CartAt J x := Iff.rfl

end GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
