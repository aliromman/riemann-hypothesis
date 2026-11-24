module

public import Mathlib
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0232
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0019
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Auxiliary
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0225
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0114
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0021
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
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UpperRamificationThirdJumpHolds
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem upper_ramification_third_jump_holds_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → SphericalInertData.Conclusion1 D' := by
  intro hL hP
  refine StepW.of_all fun K B f T w _ _ _ P x l => ?_
  refine ⟨fun _ => ∅, fun L _ _ => ?_⟩
  let T' : GlobalTheory.RowTie.WDTie (withLoc L).nd (withLoc L).naut := { l.a.A.wdT with }
  let A' : _root_.GlobalTheory.HeightCounting.AUSideAlt (withLoc L) := { l.a.A.au with }
  have cg : _root_.GlobalTheory.HeightCounting.CGTrueT hL (withLoc L) T' := { l.a.cg with }
  have au : _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL (withLoc L) T' A' := fun j h1 h2 π s σ h => l.a.au j h1 h2 π s σ h
  exact _root_.UpperTheory.BaseChangeIdentities.Conclusion1_alt_alt_alt hP.bc hP.what₂.bern hP.gen hP.std hL (withLoc L) T' A' cg au
end GlobalTheory.HeightCounting.Up
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.third_member_upper_ramification' : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → SphericalInertData.Conclusion1 D' := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.upper_ramification_third_jump_holds_alt | exact _root_.GlobalTheory.HeightCounting.Up.upper_ramification_third_jump_holds_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.upper_ramification_third_jump_holds_alt <;> assumption)
end
end
end

