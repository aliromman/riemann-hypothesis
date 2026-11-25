module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ProjBlowup

variable {X W : Scheme.{0}} {L : LB X} {m : ℕ}

def GeneratesAlong (I : W.IdealSheafData) (σ : Fin (m + 1) → L.Sec) (g : W ⟶ X) : Prop :=
  (⨆ k, g ⁻¹ᵁ L.U k = ⊤) ∧ ∀ (k : L.ι) (A : W.affineOpens) (h : A.1 ≤ g ⁻¹ᵁ L.U k),
    I.ideal A = Ideal.span (Set.range fun j => (g.appLE (L.U k) A.1 h).hom ((σ j).f k))

end GlobalTheory.ProjBlowup
