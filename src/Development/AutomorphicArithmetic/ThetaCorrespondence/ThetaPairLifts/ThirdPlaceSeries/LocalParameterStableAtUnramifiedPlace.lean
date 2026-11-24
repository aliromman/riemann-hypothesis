module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0928
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0925
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0933
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0939
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0935
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0930
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0924
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalAwayFromTypes
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0296
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0645
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0647
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0592
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0183
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0761
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0747
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0232
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0126
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0134
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0270
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0257
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0114
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0019
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0255
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Auxiliary
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0225
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0164
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalParameterStableAtUnramifiedPlace
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.HeightCounting.Up
theorem conjDualParam_stable_of_prime_not_dividing_level_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SMt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.ParameterStatement hL := by
  intro hN hM hL
  have hlift := _root_.GlobalTheory.T.liftAll_of_parIn_of_mtInput hN hL
  have hloc := _root_.GlobalTheory.T.local_component_of_par_in_third_layer hN hL
  have hsz := _root_.GlobalTheory.HeightCounting.Up.sizes_host_at_record
  refine Step.trans (Step.and (Step.and (Step.and (Step.of_evLgG (KP := KPx) (p := fun _ _ _ _ => True) hlift)
    (Step.of_evLgG hloc)) (Step.of_evLgG hsz)) hM) (Step.of_all ?_)
  rintro K B f T - hKP - ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ w hS P x l
  obtain ⟨cp⟩ := hS.1
  obtain ⟨⟨M, ad, mt⟩⟩ := h4 w hS P x
  have hpar : _root_.GlobalTheory.HeightCounting.Up.ParityConditions hL (Dof x) (cfOf x) (repOf x.r.Y) l.a.A.row := _root_.GlobalTheory.HeightCounting.Up.ParityConditions.ofSt l.a
  have hLift := h1 hKP w cp x.o.Z _ _ x.m.z x.s.p0 x.r.Y x.m.intersectionNumber_baseChange x.m.exAt x.m.inGeo x.fits.grp x.fits.grpAt l.a.A.row hpar
    M _ _ ad mt
  have hLoc := h2 hKP w cp x.o.Z _ _ x.m.z x.s.p0 x.r.Y x.m.intersectionNumber_baseChange x.m.exAt x.m.inGeo x.fits.grp x.fits.grpAt l.a.A.row hpar
  obtain ⟨-, -, -, hEFK, hCM, hDef, -⟩ := h3 hKP T w x.o.Z
  have hLaws := _root_.UpperTheory.GalN.par_laws_bare hN hL (Dof x) (cfOf x) (repOf x.r.Y) l.a.A.row l.a.A.bare hpar
  have hconds := _root_.UpperTheory.BaseChangeIdentities.Conclusion1_alt_alt_alt hN.bc hN.what₂.bern hN.gen hN.std hL (Dof x) l.a.A.wdT l.a.A.au l.a.cg l.a.au
  exact _root_.GlobalTheory.T.cuspParam_of_definite_liftAll (Dof x) l.a.A.row hLaws hconds hEFK hCM hDef hLift hLoc
end GlobalTheory.HeightCounting.Up
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parSt_of_third_layer_sMt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SMt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.ParameterStatement hL := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.conjDualParam_stable_of_prime_not_dividing_level_alt | exact _root_.GlobalTheory.HeightCounting.Up.conjDualParam_stable_of_prime_not_dividing_level_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.conjDualParam_stable_of_prime_not_dividing_level_alt <;> assumption)
end
end
end

