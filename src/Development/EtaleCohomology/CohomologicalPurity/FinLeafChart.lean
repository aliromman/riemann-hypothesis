module

public import Development.EtaleCohomology.CohomologicalPurity.LeafChartCut
public import Development.EtaleCohomology.CohomologicalPurity.LeafCoordPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafEtPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafLocPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafNbhdPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafPickPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafPolyPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafRankPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafSecPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafSpanPf

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.EtaleCohomology.CohomologicalPurity.FinLeafChart

-- ===== clump member: Development.EtaleCohomology.CohomologicalPurity.FinLeafChart =====
-- clump-header: {"m": "Development.EtaleCohomology.CohomologicalPurity.FinLeafChart", "h": "module\n\npublic import Development.EtaleCohomology.CohomologicalPurity.LeafChartCut\npublic import Development.EtaleCohomology.CohomologicalPurity.LeafCoordPf\npublic import Development.EtaleCohomology.CohomologicalPurity.LeafEtPf\npublic import Development.EtaleCohomology.CohomologicalPurity.LeafLocPf\npublic import Development.EtaleCohomology.CohomologicalPurity.LeafNbhdPf\npublic import Development.EtaleCohomology.CohomologicalPurity.LeafPickPf\npublic import Development.EtaleCohomology.CohomologicalPurity.LeafPolyPf\npublic import Development.EtaleCohomology.CohomologicalPurity.LeafRankPf\npublic import Development.EtaleCohomology.CohomologicalPurity.LeafSecPf\npublic import Development.EtaleCohomology.CohomologicalPurity.LeafShrinkPf\npublic import Development.EtaleCohomology.CohomologicalPurity.LeafSpanPf\n\n"}
section -- clump:auto
@[expose] public section

namespace LateralTheory.Fin.LeafChart

alias etale_chart_localization_property_holds := _root_.LateralTheory.CohomologicalPurity.ChartCut.LeafLoc_of
alias etale_chart_shrinking_open_property_holds := _root_.LateralTheory.CohomologicalPurity.ChartCut.LeafShrink_of
alias etale_chart_conormal_rank_property_holds := _root_.LateralTheory.CohomologicalPurity.ChartCut.LeafRank_of
alias etale_chart_generator_choice_property_holds := _root_.LateralTheory.CohomologicalPurity.ChartCut.LeafPick_of
alias etale_chart_ideal_span_property_holds := _root_.LateralTheory.CohomologicalPurity.LeafSpanPf.LeafSpan_of
alias etale_chart_etaleness_property_holds := _root_.LateralTheory.CohomologicalPurity.LeafEtPf.LeafEt_of

theorem etale_chart_coordinate_functions_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafCoord :=
  LateralTheory.CohomologicalPurity.ChartCut.LeafCoord_of
    etale_chart_conormal_rank_property_holds
    etale_chart_generator_choice_property_holds
    etale_chart_ideal_span_property_holds
    etale_chart_etaleness_property_holds

alias etale_chart_section_property_holds := _root_.LateralTheory.CohomologicalPurity.LeafSecPf.LeafSec_of
alias etale_chart_polynomial_algebra_property_holds := _root_.LateralTheory.CohomologicalPurity.LeafPolyPf.leafPoly

theorem etale_chart_neighborhood_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafNbhd :=
  LateralTheory.CohomologicalPurity.ChartCut.LeafNbhd_of
    etale_chart_section_property_holds
    etale_chart_polynomial_algebra_property_holds

theorem etale_coordinate_chart_existence : LateralTheory.CohomologicalPurity.LeafChart :=
  LateralTheory.CohomologicalPurity.ChartCut.goal_of
    etale_chart_localization_property_holds
    etale_chart_shrinking_open_property_holds
    etale_chart_coordinate_functions_property_holds
    etale_chart_neighborhood_property_holds

alias intersectionNumber_baseChange := _root_.LateralTheory.Fin.LeafChart.etale_coordinate_chart_existence

end LateralTheory.Fin.LeafChart
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.EtaleCohomology.CohomologicalPurity.FinLeafChart =====
