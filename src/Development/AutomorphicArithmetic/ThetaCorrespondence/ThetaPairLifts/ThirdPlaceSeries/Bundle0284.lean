module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0698
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0241
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CMTypeEmbeddings
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0640
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0232
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0126
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0031
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0128
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0200
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0019
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0282
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspParameterAtMemberOfParallelCopy
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0251
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0197
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0195
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0947
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0114
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0207
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0238
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0214

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CompatibleSystemTripleLayerInputs
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.RowTriple.Lay
open GlobalTheory.TwInputs Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting.FitRho
end GlobalTheory.RowTriple.Lay
namespace GlobalTheory.RowTriple.Lay
open GlobalTheory.TwInputs Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting.FitRho
end GlobalTheory.RowTriple.Lay
namespace GlobalTheory.RowTriple.Lay
open GlobalTheory.TwInputs Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting.FitRho
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem tripleLayer_inputs_at_member_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => ∃ (cf : CharFrame (w.D Z)) (Rw : RowSide (w.D Z)) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield (w.D Z).host.E)) → PlE (w.D Z).host) (S : RatDat (w.D Z).ntw) (hL' : ∀ j, ℕ → PlE (w.D Z).host → Module.End (w.D Z).what₂.LL (S.WL j)) (eig : ℕ → (w.D Z).what₂.FT → ℕ → PlE (w.D Z).host → ↥(w.D Z).LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod ((w.D Z).host.g kk)) →* (↥(w.D Z).LL0)ˣ) (_ : SideB (w.D Z) cf Rw low Pq S hL' eig θ) (Sb : Finset (PlE (w.D Z).host)), (∀ i, Sb ⊆ (w.D Z).ntw.S0 i) ∧ (∀ j, 1 ≤ j → j ≤ (w.D Z).R.m → (S.A j).IsKsForm) ∧ GlobalTheory.TwInputs.EigTrue (w.D Z) cf Rw Sb eig ∧ GlobalTheory.TwInputs.EigOcc (w.D Z) S θ hL' Sb eig ∧ GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam (w.D Z) Rw ∧ (w.D Z).nexp.sig_all ∧ (∀ a σ v, IsSplitPl (w.D Z).host v → (w.D Z).naut.locW a σ v = Rw.locR σ v) ∧ ∀ a, GlobalTheory.RowTriple.ReadTw (w.D Z) a := by
  intro hP hS hL
  refine _root_.GlobalTheory.HeightCounting.Up.Model.AtMem.at_member_imp (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.GalLoc.galois_side_at_place_alt hP hS hL)
    (_root_.GlobalTheory.HeightCounting.Up.cuspParameter_at_member_alt hP hL)) (_root_.GlobalTheory.RowTriple.Lay.EigCopy.eigenvalues_at_member_tripleLayer_alt hP hS hL))
    fun K B f T w Z Wt p0 t nch n c h => ?_
  obtain ⟨⟨⟨G, -, -, -⟩, hpar⟩, heigH⟩ := h
  have hcf : HEq (TC.cf w.I w.l Z) (cfL c.a.nt.L c.a.nt.cf) := heq_cf_of_pack c.a.nt.pack
  obtain ⟨eig, heig⟩ := exists_heq_of_eq (F := fun D : D7 => ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) c.a.nt.eq.symm
    c.a.nt.eig
  obtain ⟨θ, hθ⟩ := exists_heq_of_eq (F := fun D : D7 => ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ)
    c.a.nt.eq.symm c.a.nt.θ
  obtain ⟨Rw, hRw, ⟨Bs⟩, hloc⟩ := _root_.GlobalTheory.RowTriple.Lay.sideB_built_alt hL (w.D Z) c.a.nt.toNBuilt c.a.all.chiD.psi c.a.all.chi.psi (TC.cf w.I w.l Z) hcf
    c.a.Pq c.a.Pq_eq.symm _ c.row.S_eq.symm c.row.hecke.hL c.row.hL_eq.symm
    eig heig θ hθ
  obtain ⟨Sb, hSb, hET⟩ := heigH _ c.row.hecke.hL eig θ c.row.S_eq.symm c.row.hL_eq.symm heig hθ
  obtain ⟨hT, hO⟩ := hET Rw hRw
  have hR : ∀ a, ReadTw (withLoc c.a.nt.L) a := _root_.GlobalTheory.RowTriple.Lay.readTw_withLoc_alt hL _ c.a.nt.toNBuilt
  rw [← c.a.nt.eq] at hR
  exact ⟨TC.cf w.I w.l Z, Rw, c.a.nt.low, c.a.Pq, _, c.row.hecke.hL, eig, θ, Bs, Sb, hSb,
    _root_.GlobalTheory.RowTriple.Lay.isKsForm_of_built_heq hL (w.D Z) c.a.nt.toNBuilt _ c.row.S_eq c.a.ratIn.ks, hT, hO, hpar Rw hRw,
    _root_.GlobalTheory.Triple.IsGaloisTripleOfExpansion.sig_all G.triple, hloc, hR⟩
end GlobalTheory.RowTriple.Lay
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compatibleSystem_tripleLayer_inputs_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => ∃ (cf : CharFrame (w.D Z)) (Rw : RowSide (w.D Z)) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield (w.D Z).host.E)) → PlE (w.D Z).host) (S : RatDat (w.D Z).ntw) (hL' : ∀ j, ℕ → PlE (w.D Z).host → Module.End (w.D Z).what₂.LL (S.WL j)) (eig : ℕ → (w.D Z).what₂.FT → ℕ → PlE (w.D Z).host → ↥(w.D Z).LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod ((w.D Z).host.g kk)) →* (↥(w.D Z).LL0)ˣ) (_ : SideB (w.D Z) cf Rw low Pq S hL' eig θ) (Sb : Finset (PlE (w.D Z).host)), (∀ i, Sb ⊆ (w.D Z).ntw.S0 i) ∧ (∀ j, 1 ≤ j → j ≤ (w.D Z).R.m → (S.A j).IsKsForm) ∧ GlobalTheory.TwInputs.EigTrue (w.D Z) cf Rw Sb eig ∧ GlobalTheory.TwInputs.EigOcc (w.D Z) S θ hL' Sb eig ∧ GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam (w.D Z) Rw ∧ (w.D Z).nexp.sig_all ∧ (∀ a σ v, IsSplitPl (w.D Z).host v → (w.D Z).naut.locW a σ v = Rw.locR σ v) ∧ ∀ a, GlobalTheory.RowTriple.ReadTw (w.D Z) a := by
  first | exact @_root_.GlobalTheory.RowTriple.Lay.tripleLayer_inputs_at_member_alt | exact _root_.GlobalTheory.RowTriple.Lay.tripleLayer_inputs_at_member_alt | (intros; apply _root_.GlobalTheory.RowTriple.Lay.tripleLayer_inputs_at_member_alt <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NonGaloisTwistAtLayer
section
set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
namespace GlobalTheory.TwInputs.AtLayer
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal _root_.Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX
  NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.HeightCounting GlobalTheory.SeriesTie GlobalTheory.TwInputs.JoinModel
open Formalism.MainNotions.IntegralHeckeForms (HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
section General
variable {D : D7}
end General
section Rows
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt}
  {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)} {t : RowsT K w Z Wt p0} {nch : NChoice (w.D Z)} {n : NchT w Z Wt nch}
  {xd : ThData (w.D Z)} {c : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceCore hL t n}
end Rows
end GlobalTheory.TwInputs.AtLayer
namespace GlobalTheory.TwInputs.AtLayer
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
theorem nonempty_twOf_of_law_rx_colPin : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL (fun _ _ _ _ w Z _ _ _ _ _ c => ∀ Rw : RowSide (w.D Z), HEq Rw.locR c.a.nt.A.row.locR → GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam (w.D Z) Rw) → EvLgG fun K B f T => KPx B f → T = TwDat.untw B T.pl → ∀ w Z Wt p0 t nch n xd c, Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c) → Nonempty (RX K B f T w Z Wt p0 t) → ColPin w → Nonempty (_root_.GlobalTheory.TwInputs.TwistNormChoice hL K B f T w Z Wt p0 t nch n xd c) := by
  intro hP hS hL _
  have e1 := (evG_of_ev GlobalTheory.Mem.StdSize.vstd_size_ev).inter (evG_of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev)
  have e2 := EvG.inter (_root_.GlobalTheory.T.exists_galSide_cf_eq_cgTrue_at_members hP hS hL) (_root_.GlobalTheory.TwInputs.SmallField.fieldOk_and_exists_lamDat_ok_teich_valuesIn hP)
  refine (e1.inter e2).imp fun K _ _ _ _ H => ?_
  obtain ⟨⟨hV, hH⟩, hG, hF⟩ := H
  refine (hG.inter hF).imp fun B f T hO G hK _ w Z Wt p0 t nch n xd c ⟨e⟩ hR hC => ?_
  exact _root_.GlobalTheory.TwInputs.AtLayer.nonempty_twOf_of_hecke_stable_reads (hH := (hH (w.st Z) hO).1) (hV := (hV (w.st Z) hO).1) (hs := (hV (w.st Z) hO).2) e.1
    ((G.2 hK T w Z).1 _ t.r.z.lev.C) (G.1 hK w Z Wt p0 t nch n xd c ⟨e.1⟩ hR hC) (_root_.GlobalTheory.HeckeFamRead.exists_family_reads hP.decay hS.hkTr hS.hkRead)
end GlobalTheory.TwInputs.AtLayer
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_twOf_of_extensionWithLaw : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL (fun _ _ _ _ w Z _ _ _ _ _ c => ∀ Rw : RowSide (w.D Z), HEq Rw.locR c.a.nt.A.row.locR → GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam (w.D Z) Rw) → EvLgG fun K B f T => KPx B f → T = TwDat.untw B T.pl → ∀ w Z Wt p0 t nch n xd c, Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c) → Nonempty (RX K B f T w Z Wt p0 t) → ColPin w → Nonempty (_root_.GlobalTheory.TwInputs.TwistNormChoice hL K B f T w Z Wt p0 t nch n xd c) := by
  first | exact @_root_.GlobalTheory.TwInputs.AtLayer.nonempty_twOf_of_law_rx_colPin | exact _root_.GlobalTheory.TwInputs.AtLayer.nonempty_twOf_of_law_rx_colPin | (intros; apply _root_.GlobalTheory.TwInputs.AtLayer.nonempty_twOf_of_law_rx_colPin <;> assumption)
end
end
end

