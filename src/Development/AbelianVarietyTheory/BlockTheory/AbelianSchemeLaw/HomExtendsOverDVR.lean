module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
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

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace GlobalTheory.IndefiniteRowSideFullHecke.HomExtensionOverDVR

noncomputable abbrev genericPt (T K : Type) [CommRing T] [Field K] [Algebra T K] :
    Spec (.of K) ⟶ Spec (.of T) :=
  Spec.map (CommRingCat.ofHom (algebraMap T K))

def HomExtendsOverDVR : Prop :=
  ∀ (T : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    (K : Type) [Field K] [Algebra T K] [IsFractionRing T K]
    (G G' : Over (Spec (.of T))) [GrpObj G] [GrpObj G'],
    ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G → ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G' →
    ∀ f : (Over.pullback (genericPt T K)).obj G ⟶ (Over.pullback (genericPt T K)).obj G',
      IsMonHom f →
      ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (genericPt T K)).map F = f

end GlobalTheory.IndefiniteRowSideFullHecke.HomExtensionOverDVR
