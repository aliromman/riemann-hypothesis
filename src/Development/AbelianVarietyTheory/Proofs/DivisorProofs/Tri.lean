module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
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

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.AmpleGen

variable {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A]

def tri (n : ℤ) : ℤ := (n * n + n) / 2

def mix (L : LB A.left) (a b : ℤ) : LB A.left :=
  LB.LinComb L (K := Fin 2) ![𝟙 A.left, (GrpObj.inv : A ⟶ A).left] ![a, b]

def NV (P : LB A.left) (j : ℕ) : Prop :=
  ∃ (κ : Type) (_ : LinearOrder κ) (_ : Fintype κ) (W : κ → A.left.Opens),
    (∀ i, IsAffineOpen (W i)) ∧ ⨆ i, W i = ⊤ ∧ ¬ (GlobalTheory.AbLaw.cechLB A.hom P W).ExactAt j

end GlobalTheory.AmpleGen
