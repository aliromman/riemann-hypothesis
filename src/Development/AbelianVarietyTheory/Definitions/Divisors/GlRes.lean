module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import GroundTheory.AutomorphicForms.RealGroupsLie
public import Mathlib.RingTheory.SimpleRing.Principal
public import GroundTheory.AutomorphicForms.HarishChandraRegularity.CartanBasis
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
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

@[expose] public section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GroundTheory.Automorphic

namespace GlobalTheory.HCA

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable (E : Type) [Field E] [NumberField E] (a : ℕ)

abbrev glG : Subgroup (Matrix (Fin a) (Fin a) (Cinf E))ˣ := ⊤

abbrev glL : Submodule ℝ (Matrix (Fin a) (Fin a) (Cinf E)) := ⊤

theorem glH : IsExpLieAlgebra (glG E a) (glL E a) := isExpLieAlgebra_top

variable {E a} [_root_.NumberField.IsTotallyComplex E]

def glRes (φ : GA E a → ℂ) (x : GA E a) : glG E a → ℂ := fun y => φ (x * infGL E a y.1)

end GlobalTheory.HCA

end
