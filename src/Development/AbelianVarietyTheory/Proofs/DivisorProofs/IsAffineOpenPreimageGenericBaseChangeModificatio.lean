module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem isAffineOpen_preimage_genericBaseChange : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (G : Over M.S) (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ W : G.left.Opens, IsAffineOpen W → IsAffineOpen (α ⁻¹ᵁ W) := by
  intro R _ _ M G Y α t h W hW
  haveI := M.proper
  haveI : M.S.IsSeparated := by
    constructor
    rw [← terminal.comp_from M.π]
    infer_instance
  haveI : IsAffineHom M.gp := by
    haveI : IsAffineHom (M.gp ≫ terminal.from M.S) := inferInstance
    exact IsAffineHom.of_comp M.gp (terminal.from M.S)
  haveI : IsAffineHom α := MorphismProperty.of_isPullback (P := @IsAffineHom) h.flip inferInstance
  exact hW.preimage α

end GlobalTheory.Mum
