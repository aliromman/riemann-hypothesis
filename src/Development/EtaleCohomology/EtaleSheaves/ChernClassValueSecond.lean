module

public import Development.EtaleCohomology.EtaleSheaves.ChernClassExistence
public import Development.EtaleCohomology.EtaleSheaves.ChernClassRootLocalization
public import Development.EtaleCohomology.EtaleSheaves.ChernClassValueFirst
import Development.EtaleCohomology.TateTwists.EtaleSheafSectionsGlueOfForgetIsSheaf
public import Development.EtaleCohomology.TateTwists.ExistsNaturalEtaleKummerDegreeTwoValueOfRootsKum
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
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.ChernClassTriangleValuesFromKummerTorsor

theorem etale_kummer_chern_triangle_values_exist_of_local_roots_and_kummer_tor (hr : LateralTheory.E.ChernClassRootLocalization.LeafRootLoc) (hk : LateralTheory.E.CupProductRingLaws.LeafKumTExists) :
    LateralTheory.E.ChernClassExistence.EtaleKummerChernTriangleValuesExistNatural :=
  LateralTheory.EtaleFoundations.exists_natural_etale_kummer_degree_two_value_of_roots_kummer_gluing (LateralTheory.E.ChernClassEdgeValuesFromKummerTorsor.prim_loc_of hr) (LateralTheory.E.ChernClassEdgeValuesFromKummerTorsor.kumT_ex_of hk)
    LateralTheory.EtaleFoundations.etale_sheaf_sections_glue_of_forget_isSheaf

end LateralTheory.E.ChernClassTriangleValuesFromKummerTorsor
