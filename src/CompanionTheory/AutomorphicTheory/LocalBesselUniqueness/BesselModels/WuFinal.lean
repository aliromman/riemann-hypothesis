module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.HaarExist
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BesselLevi
public import Formalism.LocalToGlobal.SiegelLatticeTheory.BesselDiscreteSeries.BesselNVGapPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.ScWlocExists
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.NUnimodLoc
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotProdK
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.CoefLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HCReprodM
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.WFLStepsLocHNProps
public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.AtFormAdmOneOfSteps
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.AtFormAdmOne
public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.Inputs
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BesselOfWPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.BesselSplit
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocUniq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocUniqGen
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocScalarPf
import Formalism.SharpRestriction.CuspSpanNormBounds.FamilyDoubleCosetBesselBoundOfGap

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.CoefWeightedLocHolds, CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.WuFinal

-- ===== clump member: CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.CoefWeightedLocHolds =====
-- clump-header: {"m": "CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.CoefWeightedLocHolds", "h": "module\n\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BesselLevi\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.BesselDiscreteSeries.BesselNVGapPf\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.ScWlocExists\nimport Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsDS\npublic import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.NUnimodLoc\npublic import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotProdK\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.CoefLoc\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HCReprodM\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.SplitPrimeNormLemmas

namespace Formalism.L2.SG.Closed.BM

theorem CoefWeightedLoc_holds : CoefWeightedLoc := ReciprocityTheory.ChartRestriction.DS.coefWeightedLoc

theorem BesselNVGap_holds : BesselNVGap := Formalism.L2.SG.BesselDiscreteSeries.besselNVGap

theorem WlocExists_holds : WlocExists := scWlocExists Formalism.L2.SG.HCReprodM.hcReprodDSm

theorem NUnimodLoc_holds : Formalism.L2.SG.Pf.WFL.NUnimodLoc := by
  intro k r ε e f wf z0 z c hF hc hz
  exact n_unimodular_local k r ε e f wf z0 z c
    ⟨hF.ee, hF.ff, hF.ef, hF.ez, hF.fz, hF.zz, hF.ww, hF.ew, hF.fw, hF.zw⟩ hc hz

theorem QuotProdK_holds : Formalism.L2.SG.Pf.WFL.QuotProdK := quotient_product_compact

end Formalism.L2.SG.Closed.BM
end -- clump:auto
end -- clump:auto
-- ===== end clump member: CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.CoefWeightedLocHolds =====

-- ===== clump member: CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.WuFinal =====
-- clump-header: {"m": "CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.WuFinal", "h": "module\n\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.HaarExist\npublic import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.CoefWeightedLocHolds\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.WFLStepsLocHNProps\npublic import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.AtFormAdmOneOfSteps\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf\npublic import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.AtFormAdmOne\npublic import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.Inputs\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BesselOfWPf\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.BesselSplit\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocUniq\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocUniqGen\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocScalarPf\nimport Formalism.SharpRestriction.CuspSpanNormBounds.FamilyDoubleCosetBesselBoundOfGap\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace Formalism.MainNotions.BridgeCS3dBOW

open MeasureTheory Matrix Finset
open scoped InnerProductSpace
open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates Formalism.MainNotions.BridgeLemma₄
open Formalism.FourierDecayAlt.ThreeDimData Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity

theorem besselOfW_gap (hJ : CompanionTheory.Lime.BM.UniqGap) :
    Formalism.L2.SG.LocWSOf.BesselOfW := by
  intro k r z c u lam ε h H _ _ _ σ hlam hσ hgap hok hz hT hc Vp _ _ _ π hπ w hw μG μW μN ν hG hW hN hq W hWc hWeq
    hRe hne hfin
  have : CompleteSpace Vp := FiniteDimensional.completeSpace ℂ Vp
  have hS : Side k r ε lam h σ w z c u π μW μN μG ν := ⟨hlam, hσ, hgap, hok, hw, hz, hT, hc, hπ, hW, hN, hG, hq⟩
  obtain ⟨l, hlB, hla, -⟩ := CompanionTheory.Lime.BM.dDFormOne hJ CompanionTheory.Lime.BM.inputs
    k r ε lam h H σ w Vp z c u π μW μN μG ν hS
  obtain ⟨κ, hκ⟩ := bow_core hS l hla hWc hWeq hRe
  exact ⟨fun v => κ • l v, (Formalism.MainNotions.BridgeCS3d.isBesselMapSm_iff _ _ _ _ _).mpr (DDSmoothness.bessel_smul hlB κ), hκ⟩

end Formalism.MainNotions.BridgeCS3dBOW

namespace Formalism.L2.SG.Pf.WuDec.BM

open Formalism.L2.SG.SplitPrimeNormLemmas Formalism.L2.SG.WuDecay Formalism.L2.SG.Pf.WFL

theorem besselMultOneGap_of_uniqGap (hM1 : CompanionTheory.Lime.BM.UniqGap) : BesselMultOneGap := by
  intro k r ε lam h H _ _ σ z c u Wp _ _ π hok hg hl hds hz hT hc hπ B₁ B₂ hB₁ hB₂
  exact hM1 k r ε lam h H σ z c u Wp π hok.1 hg hok.2.1 hl hds hz hT hc hπ B₁ B₂
    ((Formalism.MainNotions.BridgeCS3d.isBesselMapSm_iff z _ σ π B₁).1 hB₁)
    ((Formalism.MainNotions.BridgeCS3d.isBesselMapSm_iff z _ σ π B₂).1 hB₂)

theorem wuDecay_gap (hM1 : CompanionTheory.Lime.BM.UniqGap) (hB : BesselNVGap) (hC : CoefWeightedLoc) (hW : WlocExists)
    (hQK : QuotProdK) (hNU : NUnimodLoc) (hS : LocScalarStep) : Formalism.L2.SG.Pf.WuDecayOfGap :=
  wuDecayOfGap_of_steps hC (quotAll_of hQK locHNProps_holds hNU) fun D hG X u μS νl C hQ v =>
    local_uniqueness_reduction hB hC hW (Formalism.MainNotions.BridgeCS3dBOW.besselOfW_gap hM1)
      (besselMultOneGap_of_uniqGap hM1) D hG X u μS νl C hQ v (X.Wloc u v) (X.Wloc_cont u v)
      (fun m hm h hh x => locEquiv X u v m hm h hh x) (locReprodStep_of hS D hG X u μS νl C hQ v)
      (localRepresentationL2 X u hQ v).1 (localRepresentationL2 X u hQ v).2

end Formalism.L2.SG.Pf.WuDec.BM

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Closed.BM

theorem wuDecayOfGap_of_uniqGap (h : CompanionTheory.Lime.BM.UniqGap) : WuDecayOfGap :=
  WuDec.BM.wuDecay_gap h BesselNVGap_holds CoefWeightedLoc_holds WlocExists_holds
    QuotProdK_holds NUnimodLoc_holds (@WuDec.local_scalar_reduction ⟨CoefWeightedLoc_holds⟩)

end Formalism.L2.SG.Pf
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.WuFinal =====
