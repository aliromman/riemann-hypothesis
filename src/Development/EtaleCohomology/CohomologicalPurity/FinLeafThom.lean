module

public import Development.EtaleCohomology.CohomologicalPurity.FinLeafExc
public import Development.EtaleCohomology.CohomologicalPurity.LeafBdCut
public import Development.EtaleCohomology.CohomologicalPurity.LeafPBPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafHtpyMVPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafTailNervePf
public import Development.EtaleCohomology.CohomologicalPurity.LeafTailRep0OfVec
public import Development.EtaleCohomology.CohomologicalPurity.LeafHsRelPfSplit
public import Development.EtaleCohomology.CohomologicalPurity.LeafWCovPfB
public import Development.EtaleCohomology.CohomologicalPurity.LeafWEqvLPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafTauPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafWCechPf
public import Development.EtaleCohomology.CohomologicalPurity.FreePMapMk
public import Development.EtaleCohomology.CohomologicalPurity.IsPullbackOfApp
public import Development.EtaleCohomology.CohomologicalPurity.LeafActPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafAffEqvPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafConeCokPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafDblCokPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafDeltaPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafExactPf
import Development.EtaleCohomology.CohomologicalPurity.LeafExcSpPfMono
public import Development.EtaleCohomology.CohomologicalPurity.LeafFreeCovPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafGeoPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafGoodPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafHtpyOnePf
public import Development.EtaleCohomology.CohomologicalPurity.LeafHtpyZeroPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafImgHomPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafImgPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafMonoPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafNerveSplitPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafPBMapPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafPLocPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafRepPtPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafTauNatPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafTauOf
public import Development.EtaleCohomology.CohomologicalPurity.LeafTauTopPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafUnitsRepPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafWCechRec
public import Development.EtaleCohomology.CohomologicalPurity.LeafWGmPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafWLocPf
public import Development.EtaleCohomology.CohomologicalPurity.PresSheafify
public import Development.EtaleCohomology.CohomologicalPurity.WeightedVectorLaurentEvalHomTOne
public import Development.EtaleCohomology.KummerExtensions.EtaleWeightedBlowupExceptionalChartTorsorOfEquiv

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.EtaleCohomology.CohomologicalPurity.LeafTauUPf, Development.EtaleCohomology.CohomologicalPurity.FinLeafThom

-- ===== clump member: Development.EtaleCohomology.CohomologicalPurity.LeafTauUPf =====
-- clump-header: {"m": "Development.EtaleCohomology.CohomologicalPurity.LeafTauUPf", "h": "module\n\npublic import Development.EtaleCohomology.CohomologicalPurity.LeafTauPf\npublic import Development.EtaleCohomology.CohomologicalPurity.LeafTauOf\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

theorem tail_fst (d : ℕ) (R : Type) [CommRing R] :
    (prod.map (Pj.tail d) (𝟙 _) : PR (d + 1) 1 R ⟶ PR d 0 R) ≫ prod.fst ≫ Pj.line d 0 =
      prod.fst ≫ Pj.line (d + 1) 1 := by
  rw [prod.map_fst_assoc, Pj.tail_line]

theorem pull_hyp (h6 : DivisorNaturality) (q : ℕ) [NeZero q] (d : ℕ) (R : Type) [CommRing R] (hI : Inv q (PR d 0 R)) :
    pull _ (prod.map (Pj.tail d) (𝟙 _) : PR (d + 1) 1 R ⟶ PR d 0 R) _ _ (hyp q d 0 R) = hyp q (d + 1) 1 R := by
  unfold hyp
  rw [(h6 q).2.2.1 _ _ hI, tail_fst]

theorem tail_poly (hG : LeafGeo) (h6 : DivisorNaturality) (q : ℕ) [NeZero q] (d : ℕ) (R : Type) [CommRing R]
    (hq : IsUnit (q : R)) (n i : ℤ) (a : ∀ j : Fin d, Ht q (sp R) (n - 2 * (j : ℕ)) (i - (j : ℕ))) :
    pull _ (prod.map (Pj.tail d) (𝟙 _) : PR (d + 1) 1 R ⟶ PR d 0 R) (tw q i) n (poly q d 0 R d n i a) =
      poly q (d + 1) 1 R d n i a := by
  have hI := hG.2.1 q d 0 R hq
  unfold poly

  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pull_cast, (h6 q).1, ← pull_comp, prod.map_snd, Category.comp_id, pull_cpow h6 q _ hI, pull_hyp h6 q d R hI]

theorem LeafTauU_of (hG : LeafGeo) : LeafTauU := by
  intro hPB hTl H q _ d R _ hq n i
  have h6 : DivisorNaturality := H.2.2.2.2.1
  have hb := (hTl H q d R hq i n).comp (hPB H.1 h6 H.2.2.2.2.2.2.2.2.2.2.1 q d R hq n i)
  convert hb using 1
  funext a
  exact (tail_poly hG h6 q d R hq n i a).symm

end LateralTheory.CohomologicalPurity.Thom
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.EtaleCohomology.CohomologicalPurity.LeafTauUPf =====

-- ===== clump member: Development.EtaleCohomology.CohomologicalPurity.FinLeafThom =====
-- clump-header: {"m": "Development.EtaleCohomology.CohomologicalPurity.FinLeafThom", "h": "module\n\npublic import Development.EtaleCohomology.CohomologicalPurity.FinLeafExc\npublic import Development.EtaleCohomology.CohomologicalPurity.LeafBdCut\npublic import Development.EtaleCohomology.CohomologicalPurity.LeafPBPf\npublic import Development.EtaleCohomology.CohomologicalPurity.LeafHtpyMVPf\npublic import Development.EtaleCohomology.CohomologicalPurity.LeafTailNervePf\npublic import Development.EtaleCohomology.CohomologicalPurity.LeafTailRep0OfVec\npublic import Development.EtaleCohomology.CohomologicalPurity.LeafHsRelPfSplit\npublic import Development.EtaleCohomology.CohomologicalPurity.LeafWCovPfB\npublic import Development.EtaleCohomology.CohomologicalPurity.LeafWEqvLPf\npublic import Development.EtaleCohomology.CohomologicalPurity.LeafTauPf\npublic import Development.EtaleCohomology.CohomologicalPurity.LeafWCechPf\npublic import Development.EtaleCohomology.CohomologicalPurity.FreePMapMk\npublic import Development.EtaleCohomology.CohomologicalPurity.IsPullbackOfApp\npublic import Development.EtaleCohomology.CohomologicalPurity.LeafActPf\npublic import Development.EtaleCohomology.CohomologicalPurity.LeafAffEqvPf\npublic import Development.EtaleCohomology.CohomologicalPurity.LeafConeCokPf\npublic import Development.EtaleCohomology.CohomologicalPurity.LeafDblCokPf\npublic import Development.EtaleCohomology.CohomologicalPurity.LeafDeltaPf\npublic import Development.EtaleCohomology.CohomologicalPurity.LeafExactPf\nimport Development.EtaleCohomology.CohomologicalPurity.LeafExcSpPfMono\npublic import Development.EtaleCohomology.CohomologicalPurity.LeafFreeCovPf\npublic import Development.EtaleCohomology.CohomologicalPurity.LeafGeoPf\npublic import Development.EtaleCohomology.CohomologicalPurity.LeafGoodPf\npublic import Development.EtaleCohomology.CohomologicalPurity.LeafHtpyOnePf\npublic import Development.EtaleCohomology.CohomologicalPurity.LeafHtpyZeroPf\npublic import Development.EtaleCohomology.CohomologicalPurity.LeafImgHomPf\npublic import Development.EtaleCohomology.CohomologicalPurity.LeafImgPf\npublic import Development.EtaleCohomology.CohomologicalPurity.LeafMonoPf\npublic import Development.EtaleCohomology.CohomologicalPurity.LeafNerveSplitPf\npublic import Development.EtaleCohomology.CohomologicalPurity.LeafPBMapPf\npublic import Development.EtaleCohomology.CohomologicalPurity.LeafPLocPf\npublic import Development.EtaleCohomology.CohomologicalPurity.LeafRepPtPf\npublic import Development.EtaleCohomology.CohomologicalPurity.LeafTauNatPf\npublic import Development.EtaleCohomology.CohomologicalPurity.LeafTauOf\npublic import Development.EtaleCohomology.CohomologicalPurity.LeafTauTopPf\npublic import Development.EtaleCohomology.CohomologicalPurity.LeafTauUPf\npublic import Development.EtaleCohomology.CohomologicalPurity.LeafUnitsRepPf\npublic import Development.EtaleCohomology.CohomologicalPurity.LeafWCechRec\npublic import Development.EtaleCohomology.CohomologicalPurity.LeafWGmPf\npublic import Development.EtaleCohomology.CohomologicalPurity.LeafWLocPf\npublic import Development.EtaleCohomology.CohomologicalPurity.PresSheafify\npublic import Development.EtaleCohomology.CohomologicalPurity.WeightedVectorLaurentEvalHomTOne\npublic import Development.EtaleCohomology.KummerExtensions.EtaleWeightedBlowupExceptionalChartTorsorOfEquiv\n\n"}
section -- clump:auto
@[expose] public section

namespace LateralTheory.Fin.LeafThom

theorem etale_boundary_monomorphism_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Bd.LeafMono :=
  LateralTheory.CohomologicalPurity.Bd.LeafMono_of

theorem etale_boundary_good_pair_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Bd.LeafGood :=
  LateralTheory.CohomologicalPurity.Bd.LeafGood_of

theorem etale_boundary_connecting_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Bd.LeafDelta :=
  LateralTheory.CohomologicalPurity.Bd.LeafDelta_of

theorem etale_boundary_exact_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Bd.LeafExact :=
  LateralTheory.CohomologicalPurity.Bd.LeafExact_of

theorem etale_boundary_generator_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Bd.LeafGen :=
  LateralTheory.CohomologicalPurity.Bd.LeafGen_of

theorem etale_boundary_image_hom_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Bd.LeafImgHom :=
  LateralTheory.CohomologicalPurity.Bd.LeafImgHom_of etale_boundary_generator_of_thom_isomorphism

theorem etale_boundary_image_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Bd.LeafImg :=
  LateralTheory.CohomologicalPurity.Bd.LeafImg_of etale_boundary_image_hom_of_thom_isomorphism

theorem etale_boundary_map_of_thom_isomorphism : LateralTheory.CohomologicalPurity.LeafBd :=
  LateralTheory.CohomologicalPurity.Bd.goal_of
    etale_boundary_monomorphism_of_thom_isomorphism
    LateralTheory.CohomologicalPurity.Bd.LeafPush_of
    etale_boundary_good_pair_of_thom_isomorphism
    etale_boundary_connecting_of_thom_isomorphism
    etale_boundary_exact_of_thom_isomorphism
    etale_boundary_image_of_thom_isomorphism

theorem etale_thom_geometric_fibers_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Thom.LeafGeo :=
  LateralTheory.CohomologicalPurity.Thom.LeafGeo_of

theorem etale_thom_group_action_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Thom.LeafAct :=
  LateralTheory.CohomologicalPurity.Thom.LeafAct_of

theorem etale_thom_pullback_map_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Thom.LeafPBMap :=
  LateralTheory.CohomologicalPurity.Thom.LeafPBMap_of

theorem etale_affine_bundle_equivalence_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Thom.LeafAffEqv :=
  LateralTheory.CohomologicalPurity.Thom.LeafAffEqv_of

theorem etale_thom_pullback_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Thom.LeafPB :=
  LateralTheory.CohomologicalPurity.Thom.LeafPB_of
    etale_thom_geometric_fibers_of_thom_isomorphism
    etale_thom_pullback_map_of_thom_isomorphism
    etale_affine_bundle_equivalence_of_thom_isomorphism

theorem etale_affine_line_homotopy_zero_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Thom.LeafHtpyZero :=
  LateralTheory.CohomologicalPurity.Thom.LeafHtpyZero_of

theorem etale_affine_line_homotopy_one_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Thom.LeafHtpyOne :=
  LateralTheory.CohomologicalPurity.Thom.LeafHtpyOne_of

theorem etale_free_covering_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Thom.LeafFreeCov :=
  LateralTheory.CohomologicalPurity.FreeCovPf.LeafFreeCov_of

theorem etale_homotopy_mayer_vietoris_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Thom.LeafHtpyMV :=
  LateralTheory.CohomologicalPurity.Thom.LeafHtpyMV_of etale_free_covering_of_thom_isomorphism

theorem etale_affine_homotopy_invariance_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Thom.LeafHtpy :=
  LateralTheory.CohomologicalPurity.Thom.LeafHtpy_of
    etale_affine_line_homotopy_zero_of_thom_isomorphism
    etale_affine_line_homotopy_one_of_thom_isomorphism
    etale_homotopy_mayer_vietoris_of_thom_isomorphism

theorem etale_nerve_split_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Thom.LeafNerveSplit :=
  LateralTheory.CohomologicalPurity.Thom.LeafNerveSplit_of

theorem etale_units_representable_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Thom.LeafUnitsRep :=
  LateralTheory.CohomologicalPurity.Thom.LeafUnitsRep_of

theorem etale_thom_tail_nerve_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Thom.LeafTailNerve :=
  LateralTheory.CohomologicalPurity.Thom.LeafTailNerve_of
    etale_nerve_split_of_thom_isomorphism
    etale_units_representable_of_thom_isomorphism

theorem etale_thom_representable_point_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Thom.LeafRepPt :=
  LateralTheory.CohomologicalPurity.Thom.LeafRepPt_of

theorem etale_thom_tail_representable_degree_zero_of_thom_isomorphism :
    LateralTheory.CohomologicalPurity.Thom.LeafTailRep0 :=
  LateralTheory.CohomologicalPurity.Thom.LeafTailRep0_of etale_thom_representable_point_of_thom_isomorphism

theorem etale_thom_tail_representable_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Thom.LeafTailRep :=
  LateralTheory.CohomologicalPurity.Thom.LeafTailRep_of
    etale_thom_tail_nerve_of_thom_isomorphism
    etale_thom_tail_representable_degree_zero_of_thom_isomorphism

theorem etale_thom_tail_vanishing_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Thom.LeafTail :=
  LateralTheory.CohomologicalPurity.Thom.LeafTail_of
    etale_thom_tail_representable_of_thom_isomorphism
    etale_affine_homotopy_invariance_of_thom_isomorphism

theorem etale_thom_class_unit_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Thom.LeafTauU :=
  LateralTheory.CohomologicalPurity.Thom.LeafTauU_of etale_thom_geometric_fibers_of_thom_isomorphism

theorem etale_thom_class_top_degree_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Thom.LeafTauTop :=
  LateralTheory.CohomologicalPurity.Thom.LeafTauTop_of

theorem etale_thom_class_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Thom.LeafTau :=
  LateralTheory.CohomologicalPurity.Thom.ThomClassRestriction.LeafTau_of
    etale_boundary_map_of_thom_isomorphism
    etale_thom_geometric_fibers_of_thom_isomorphism
    etale_thom_pullback_of_thom_isomorphism
    etale_thom_tail_vanishing_of_thom_isomorphism
    etale_thom_class_unit_of_thom_isomorphism
    etale_thom_class_top_degree_of_thom_isomorphism

theorem etale_thom_class_natural_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Thom.LeafTauNat :=
  LateralTheory.CohomologicalPurity.Thom.LeafTauNat_of etale_thom_geometric_fibers_of_thom_isomorphism

theorem etale_cokernel_isomorphism_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Thom.ExcSp.LeafCokIso :=
  LateralTheory.CohomologicalPurity.Thom.ExcSp.LeafCokIso_of

theorem etale_double_cokernel_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Thom.ExcSp.LeafDblCok :=
  LateralTheory.CohomologicalPurity.Thom.ExcSp.leafDblCok_of

theorem etale_mapping_cone_cokernel_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Thom.ExcSp.LeafConeCok :=
  LateralTheory.CohomologicalPurity.Thom.ExcSp.leafConeCok_of

theorem etale_relative_homotopy_sequence_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Thom.ExcSp.LeafHsRel :=
  LateralTheory.CohomologicalPurity.Thom.ExcSp.etale_relative_cohomology_iso_of_cone_and_double_cokernel_isos
    etale_mapping_cone_cokernel_of_thom_isomorphism
    etale_double_cokernel_of_thom_isomorphism

theorem etale_thom_excision_specialization_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Thom.LeafExcSp :=
  LateralTheory.CohomologicalPurity.Thom.ExcSp.etaleSplitExcision_of_cokernel_relative
    etale_cokernel_isomorphism_of_thom_isomorphism
    etale_relative_homotopy_sequence_of_thom_isomorphism

theorem etale_chart_projective_localization_of_thom_isomorphism :
    LateralTheory.CohomologicalPurity.Thom.ExcP.Chart.LeafPLoc :=
  LateralTheory.CohomologicalPurity.Thom.ExcP.Chart.LeafPLoc_of

theorem etale_chart_localization_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Thom.ExcP.Chart.LeafWLoc :=
  LateralTheory.CohomologicalPurity.Thom.ExcP.Chart.LeafWLoc_of

theorem etale_chart_covering_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Thom.ExcP.Chart.LeafWCov :=
  LateralTheory.CohomologicalPurity.Thom.ExcP.Chart.LeafWCov_of'
    etale_thom_geometric_fibers_of_thom_isomorphism
    etale_chart_projective_localization_of_thom_isomorphism
    etale_chart_localization_of_thom_isomorphism

theorem etale_chart_gluing_data_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Thom.ExcP.Chart.LeafWData :=
  LateralTheory.CohomologicalPurity.Thom.ExcP.Chart.LeafWData_of

theorem etale_chart_cech_descent_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Thom.ExcP.Chart.LeafWCech :=
  LateralTheory.CohomologicalPurity.Thom.ExcP.Chart.LeafWCech_of_data etale_chart_gluing_data_of_thom_isomorphism

theorem etale_chart_right_equivalence_of_thom_isomorphism :
    LateralTheory.CohomologicalPurity.Thom.ExcP.Chart.LeafWEqvR :=
  LateralTheory.CohomologicalPurity.Thom.ExcP.Chart.LeafWEqvR_of etale_chart_cech_descent_of_thom_isomorphism

theorem etale_chart_multiplicative_group_action_of_thom_isomorphism :
    LateralTheory.CohomologicalPurity.Thom.ExcP.Chart.LeafWGm :=
  LateralTheory.CohomologicalPurity.Thom.ExcP.Chart.LeafWGm_of

theorem etale_chart_torsor_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Thom.ExcP.Chart.LeafWTors :=
  WeightedBlowupChartPointUnits.Cb.etale_weighted_blowup_exceptional_chart_torsor_of_equivalence
    etale_chart_right_equivalence_of_thom_isomorphism
    etale_thom_geometric_fibers_of_thom_isomorphism
    etale_boundary_map_of_thom_isomorphism
    etale_thom_excision_specialization_of_thom_isomorphism
    LateralTheory.Fin.LeafExc.intersectionNumber_baseChange

theorem etale_chart_left_equivalence_of_thom_isomorphism :
    LateralTheory.CohomologicalPurity.Thom.ExcP.Chart.LeafWEqvL :=
  LateralTheory.CohomologicalPurity.Thom.ExcP.Chart.LeafWEqvL_of
    etale_chart_multiplicative_group_action_of_thom_isomorphism
    etale_chart_torsor_of_thom_isomorphism

theorem etale_thom_chart_factorization_of_thom_isomorphism :
    LateralTheory.CohomologicalPurity.Thom.ExcP.LeafChartFact :=
  LateralTheory.CohomologicalPurity.Thom.ExcP.LeafChartFact_of
    etale_thom_geometric_fibers_of_thom_isomorphism
    etale_chart_covering_of_thom_isomorphism
    etale_chart_right_equivalence_of_thom_isomorphism
    etale_chart_left_equivalence_of_thom_isomorphism

theorem etale_thom_excision_projective_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Thom.LeafExcP :=
  LateralTheory.CohomologicalPurity.Thom.excision_of_thom_chart_factorization
    etale_boundary_map_of_thom_isomorphism
    etale_thom_excision_specialization_of_thom_isomorphism
    etale_thom_chart_factorization_of_thom_isomorphism

theorem etale_thom_isomorphism_of_thom_isomorphism : LateralTheory.CohomologicalPurity.LeafThom :=
  LateralTheory.CohomologicalPurity.Thom.goal_of
    etale_thom_geometric_fibers_of_thom_isomorphism
    etale_thom_group_action_of_thom_isomorphism
    etale_thom_class_of_thom_isomorphism
    etale_thom_class_natural_of_thom_isomorphism
    etale_thom_excision_projective_of_thom_isomorphism

theorem intersectionNumber_baseChange : LateralTheory.CohomologicalPurity.LeafThom :=
  etale_thom_isomorphism_of_thom_isomorphism

end LateralTheory.Fin.LeafThom
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.EtaleCohomology.CohomologicalPurity.FinLeafThom =====
