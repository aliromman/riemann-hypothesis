module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

theorem hom_ext_of_geometric_points (S X Z : Scheme.{0}) [IsReduced S] (q : X ⟶ Z)
    [IsSeparated q] (f g : S ⟶ X) (hq : f ≫ q = g ≫ q)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S), x ≫ f = x ≫ g) : f = g := by
  have hs : Surjective (equalizer.ι f g) := ⟨fun s => by
    let k := AlgebraicClosure (S.residueField s)
    let x : Sp k ⟶ S :=
      Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) k)) ≫ S.fromSpecResidueField s
    have hx := h k x
    let p : Sp k := IsLocalRing.closedPoint k
    refine ⟨equalizer.lift x hx p, ?_⟩
    rw [← Scheme.Hom.comp_apply, equalizer.lift_ι]
    simp only [x, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply _ _⟩
  exact ext_of_isDominant_of_isSeparated q hq (equalizer.ι f g) (equalizer.condition _ _)

end GlobalTheory.HkFam
