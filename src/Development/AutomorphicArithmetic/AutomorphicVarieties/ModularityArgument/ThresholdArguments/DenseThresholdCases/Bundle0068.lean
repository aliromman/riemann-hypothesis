module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.PsiCont
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.AuArith
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.PtLaws
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0029
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0028
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0030
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutQN
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0064
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgOfCyc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0036
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0063
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.WeakOfAtt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.FirstConditionUp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0056
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WinTop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0052

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DnPmDown
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp
open UpperTheory.V.Z.Win in
theorem UpperTheory.V.Z.Win.Dn.pmDown_alt :
    _root_.UpperTheory.V.Ws.UnramifiedInputs → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (ι : PadicAlgCl l ≃+* ℂ) (y : X.A →ₐ[c'.O] PadicAlgCl l),
        T.Wts (fun i => 2 * D.wts4 i) (X.P.map (y : X.A →+* PadicAlgCl l)) →
        ∀ r : G ℚ Ω →* M4 (PadicAlgCl l), r.comp (resQ T.F) = (X.P.map (y : X.A →+* PadicAlgCl l)).r → Continuous r → D.Mult r →
          Irr (r.comp T.L.fixingSubgroup.subtype) → _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (Af.tw (r.comp (resQ T.L)).toHomUnits (W.pushCh (algebraMap c'.O (PadicAlgCl l)) K.κ)) → _root_.UpperTheory.V.Aut.IsAut4Alt ι r := by
  intro U Ω _ _ _ l _ c D T hF _ c' h K X ι y hW r hr hc hm hi h1
  have hG : D.Good := hF.2.elim (fun a => a.1.1) (fun a => a.1.1)
  obtain ⟨hi1, -⟩ := auIrr _ (r.comp (resQ T.L)) hi fun g =>
    ⟨IntermediateField.fixingSubgroupEquiv T.L g, rfl⟩
  have h2 := (_root_.UpperTheory.GalN.V.automorphy_bridge_of_printed_hida U.pr T.L Ω l ι 4 _).2.2 h1
  have hκ := _root_.UpperTheory.V.Ws.isAlgChar_pushCh_link_kappa U.pr D T c' h K ι
  have hN := _root_.UpperTheory.GalN.V.csdN'_alt U.pr.toClassicalTheorems (by norm_num) h1
  have hκc : Continuous (W.pushCh (algebraMap c'.O (PadicAlgCl l)) K.κ) := hκ.choose_spec.1
  have hcr : Continuous r.toHomUnits := Units.continuous_iff.2 ⟨hc, hc.comp continuous_inv⟩
  have hW3 := _root_.UpperTheory.V.Z.Win.Dn.twist'_alt U.pr.toClassicalTheorems ((_root_.UpperTheory.V.Af.algOfCyc_s U.pr T.L Ω l ι).2.1 _ _ hκ hκ).2 hκc.inv
    (hN.2 (Af.Bc.irrBasic.2 _ _ _ _ _ (hcr.comp (Af.continuous_restrictScalarsHom ℚ T.L Ω)) hκc))
  have h3 := _root_.UpperTheory.V.Af.twist_invariance_automorphic U.pr T.L Ω l ι 4 _ _ h2 ((_root_.UpperTheory.V.Af.algOfCyc_s U.pr T.L Ω l ι).2.1 _ _ hκ hκ).2
  have h4 : Af.tw (Af.tw (r.comp (resQ T.L)).toHomUnits (W.pushCh (algebraMap c'.O (PadicAlgCl l)) K.κ))
      (W.pushCh (algebraMap c'.O (PadicAlgCl l)) K.κ)⁻¹ = r.toHomUnits.comp (Af.resG ℚ T.L Ω) := by
    ext g : 2
    rw [Af.tw_val, Af.tw_val, smul_smul, MonoidHom.inv_apply, Units.inv_mul, one_smul]
    rfl
  rw [h4] at h3 hW3
  obtain ⟨hgal, hsol⟩ := auGal D T
  obtain ⟨P, hP⟩ := auPair r (W.pushCh (algebraMap c.O (PadicAlgCl l)) D.th) hm 1
  have h0 := _root_.UpperTheory.GalN.V.isAutomorphicOverImagQuad_of_restriction_aut_irr U.pr (Z.Bc.solC_of_solDescent (_root_.UpperTheory.V.Af.solvable_descent_of_printed_hida U.pr)) Ω T.K T.L (T.hL ▸ le_sup_right) T.degK hgal hsol l ι 4
    (by norm_num) r.toHomUnits (W.pushCh (algebraMap c.O (PadicAlgCl l)) D.th)
    (Units.continuous_iff.2 ⟨hc, hc.comp continuous_inv⟩) (_root_.UpperTheory.V.Ws.isAlgChar_pushCh_th_of_good U.pr D hG ι)
    ⟨P, fun s => by simpa using hP s⟩ hi1 h3
  obtain ⟨hI, hFl, hU⟩ := UpperTheory.V.Keep.ptLaws D T hG hF.1 hF.1.locL c' h X y hW r hr
  have hle : T.K ≤ T.L := T.hL ▸ le_sup_right
  letI : Algebra T.K T.L := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower T.K T.L Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ℚ T.K T.L := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  haveI : IsGalois T.K T.L := IsGalois.tower_top_of_isGalois ℚ T.K T.L
  haveI : Group.IsSolvable (T.L ≃ₐ[ℚ] T.L) := hsol
  have s2 : Group.IsSolvable (T.L ≃ₐ[T.K] T.L) :=
    Group.isSolvable_of_isSolvable_injective (f := (AlgEquiv.restrictScalarsHom ℚ : (T.L ≃ₐ[T.K] T.L) →* (T.L ≃ₐ[ℚ] T.L)))
      (AlgEquiv.restrictScalars_injective ℚ)
  have e : (r.toHomUnits.comp (Af.resG ℚ T.K Ω)).comp (Af.resG T.K T.L Ω) = r.toHomUnits.comp (Af.resG ℚ T.L Ω) := rfl
  have i2 : Af.IsIrr ((r.toHomUnits.comp (Af.resG ℚ T.K Ω)).comp (Af.resG T.K T.L Ω)) := e ▸ hi1
  have i1 : Af.IsIrr (r.toHomUnits.comp (Af.resG ℚ T.K Ω)) := (Af.Bc.irrBasic.1 _ _ _ 4 _).1 _ i2
  have hcK : Continuous (r.toHomUnits.comp (Af.resG ℚ T.K Ω)) := hcr.comp (Af.continuous_restrictScalarsHom ℚ T.K Ω)
  obtain ⟨Q, hQ⟩ := auPair r (W.pushCh (algebraMap c.O (PadicAlgCl l)) D.th) hm D.cc
  have hpol : Af.Sol.Pol ι (r.toHomUnits.comp (Af.resG ℚ T.K Ω)) :=
    ⟨ℚ, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, _, D.cc, Q, _root_.UpperTheory.V.Ws.isAlgChar_pushCh_th_of_good U.pr D hG ι, auSign _, hG.isCC, fun s s' h => by
        have h' : Af.resG ℚ T.K Ω s' = D.cc * Af.resG ℚ T.K Ω s * D.cc⁻¹ := h
        rw [MonoidHom.comp_apply, MonoidHom.comp_apply, h']
        exact hQ _⟩
  have fl := (flagLaws ℚ Ω l 4 r.toHomUnits).2.2.2 T.K
  have hWK : _root_.UpperTheory.V.Z.Win.WitA ι (r.toHomUnits.comp (Af.resG ℚ T.K Ω)) :=
    _root_.UpperTheory.V.Z.Win.Dn.down'_alt T.L U.pr s2 (by norm_num) hcK i2 hpol (h0 hcr T.K T.degK i1) (fl.2.1 hFl) (fl.1 hI) (fun w hw _ => hU w hw) (e ▸ hW3)
  exact _root_.UpperTheory.GalN.V.isAutQA_of_isAutomorphicOverImagQuad_of_witAQ h0 fun _ => _root_.UpperTheory.V.Z.Win.Dn.across'_alt U.pr T.K Ω T.degK (by norm_num)
    (fun A hA g hg x => (IntermediateField.mem_fixingSubgroup_iff _ _).1 (hF.1.split l hG.l_mem A hA hg) x x.2) hcr h0
    ⟨_, _root_.UpperTheory.V.Ws.isAlgChar_pushCh_th_of_good U.pr D hG ι, P, fun s => by simpa using hP s⟩ hI hFl i1 hWK
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.FirstConditionUp
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.Zero.LLC UpperTheory.V.Af UpperTheory.V.Z.Gam
open UpperTheory.GalN.V GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter UpperTheory.V.Af.Bc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Win
private theorem unlocked_of_potentially {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    {r : G F Ω →* GL (Fin n) (Qbar l)} {v : HeightOneSpectrum (𝓞 F)} (h : PotUnl r v) : Unl1 r v := fun A hA =>
  (h A hA).imp fun _ k => ⟨k.1, fun i j e => k.2 i j 1 le_rfl (by simpa only [pow_one] using e)⟩
private theorem keeps_of_pot (hFL : FlagLaws) {K M Ω : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Field Ω] [CharZero Ω]
    [IsAlgClosure ℚ Ω] [Algebra K Ω] [Algebra K M] [Algebra M Ω] [IsScalarTower K M Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    (r : G ℚ Ω →* GL (Fin n) (Qbar l))
    (hp : ∀ v : HeightOneSpectrum (𝓞 ℚ), ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → PotUnl r v) :
    Keeps (r.comp (resG ℚ K Ω)) M := by
  intro w hw _
  have hv : ((l : ℕ) : 𝓞 ℚ) ∈ (w.under (𝓞 ℚ)).asIdeal := by
    simpa [HeightOneSpectrum.under, Ideal.mem_comap] using hw
  have h := (((hFL ℚ Ω l n r).2.2.2 M).2.2 w hw).1 (hp _ hv)
  exact unlocked_of_potentially h
private theorem step (hFL : FlagLaws) (hUD : _root_.UpperTheory.V.Z.Win.AUpDownAlt) (hP : _root_.UpperTheory.V.Af.HypothesesH') (hR : RowT) (K K' Ω : Type) [Field K] [NumberField K] [IsCMField K]
    [Field K'] [NumberField K'] [IsCMField K'] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω] [Algebra K' Ω]
    (hK : Module.finrank ℚ K = 2) (hK' : Module.finrank ℚ K' = 2) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (hn : 1 ≤ n)
    (r : G ℚ Ω →* GL (Fin n) (Qbar l)) (hp : ∀ v : HeightOneSpectrum (𝓞 ℚ), ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → PotUnl r v)
    (hc : Continuous r) (hA : IsAutomorphicOverImagQuad ι r)
    (θ : G ℚ Ω →* (Qbar l)ˣ) (hθ : IsAlgChar ι θ) (hd : DualTw r θ) (hI : IneAb r) (hF : Flagged r)
    (hi : IsIrr (r.comp ((resG ℚ K Ω).range ⊓ (resG ℚ K' Ω).range).subtype))
    (hW : WitA ι (r.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω))) :
    WitA ι (r.comp (AlgEquiv.restrictScalarsHom ℚ : G K' Ω →* G ℚ Ω)) := by
  obtain ⟨M, _, _, _, iK, iK', iM, tK, tK', gK, gK', hs, hs', hM, hM'⟩ := UpperTheory.V.Z.Bc.biQuad K K' Ω hK hK'
  have closure_over (L : Type) [Field L] [CharZero L] [Algebra L Ω] : IsAlgClosure L Ω :=
    ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) L⟩
  have := closure_over K
  have := closure_over K'
  have := closure_over M
  have exists_conj : ∃ c : G ℚ Ω, IsConjEl c := by
    let j : Ω →ₐ[ℚ] ℂ := _root_.IsAlgClosed.lift
    let : Algebra Ω ℂ := j.toRingHom.toAlgebra
    have : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
    let τ : ℂ ≃ₐ[ℚ] ℂ := AlgEquiv.ofRingEquiv (f := starRingAut) fun x => by simp
    exact ⟨τ.restrictNormal Ω, algebraMap Ω ℂ, τ.restrictNormal_commutes Ω⟩
  obtain ⟨c, hcc⟩ := exists_conj
  have he : (r.comp (resG ℚ K Ω)).comp (resG K M Ω) = (r.comp (resG ℚ K' Ω)).comp (resG K' M Ω) :=
    MonoidHom.ext fun s => rfl
  have irr_of_range {Δ Δ' : Type} [Group Δ] [Group Δ']
      (f : Δ →* G ℚ Ω) (f' : Δ' →* G ℚ Ω) (h : ∀ s, ∃ t, f' t = f s)
      (H : IsIrr (r.comp f)) : IsIrr (r.comp f') := by
    refine ⟨H.1, fun _ _ _ => trivial, fun W hW hI => H.2.2 W hW fun s v hv => ?_⟩
    obtain ⟨t, ht⟩ := h s
    simpa only [MonoidHom.comp_apply, ht] using hI t v hv
  have hiM : IsIrr ((r.comp (resG ℚ K Ω)).comp (resG K M Ω)) := by
    refine irr_of_range _ ((resG ℚ K Ω).comp (resG K M Ω)) ?_ hi
    rintro ⟨s, ⟨t, rfl⟩, h2⟩
    obtain ⟨u, rfl⟩ := (hM t).2 h2
    exact ⟨u, rfl⟩
  have hiM' : IsIrr ((r.comp (resG ℚ K' Ω)).comp (resG K' M Ω)) := he ▸ hiM
  have hiK : IsIrr (r.comp (resG ℚ K Ω)) :=
    irr_of_range ((resG ℚ K Ω).comp (resG K M Ω)) (resG ℚ K Ω) (fun s => ⟨resG K M Ω s, rfl⟩) hiM
  have hiK' : IsIrr (r.comp (resG ℚ K' Ω)) :=
    irr_of_range ((resG ℚ K' Ω).comp (resG K' M Ω)) (resG ℚ K' Ω) (fun s => ⟨resG K' M Ω s, rfl⟩) hiM'
  have exists_pairing (F : Type) [Field F] [CharZero F] [Algebra F Ω] :
      ∃ P, IsPairing c (r.comp (resG ℚ F Ω)) (θ.comp (resG ℚ F Ω)) P := by
    obtain ⟨J, hJ⟩ := hd
    refine ⟨J * r c⁻¹, fun s s' h => ?_⟩
    have h' : resG ℚ F Ω s' = c * resG ℚ F Ω s * c⁻¹ := h
    have e : r c⁻¹ * r (resG ℚ F Ω s') = r (resG ℚ F Ω s) * r c⁻¹ := by
      rw [h', ← map_mul, ← map_mul]
      congr 1
      group
    have e' : (r c⁻¹).val * (r (resG ℚ F Ω s')).val = (r (resG ℚ F Ω s)).val * (r c⁻¹).val :=
      congrArg Units.val e
    have hp := hJ (resG ℚ F Ω s)
    simp only [MonoidHom.comp_apply]
    rw [Units.val_mul, ← Matrix.smul_mul, ← hp]
    simp only [Matrix.mul_assoc, e']
  obtain ⟨P, hPa⟩ := exists_pairing K
  obtain ⟨P', hPa'⟩ := exists_pairing K'
  have pol : Sol.Pol ι (r.comp (resG ℚ K Ω)) :=
    ⟨ℚ, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      θ, c, P, hθ, UpperTheory.V.Ws.auSign θ, hcc, hPa⟩
  have pol' : Sol.Pol ι (r.comp (resG ℚ K' Ω)) :=
    ⟨ℚ, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      θ, c, P', hθ, UpperTheory.V.Ws.auSign θ, hcc, hPa'⟩
  have up := (hUD hP hR K M Ω hs l ι n hn (r.comp (resG ℚ K Ω)) (hc.comp (continuous_restrictScalarsHom ℚ K Ω)) hiM pol
    (hA hc K hK hiK) (((hFL ℚ Ω l n r).2.2.2 K).2.1 hF)).1 hW
  rw [he] at up
  exact (hUD hP hR K' M Ω hs' l ι n hn (r.comp (resG ℚ K' Ω)) (hc.comp (continuous_restrictScalarsHom ℚ K' Ω)) hiM' pol'
    (hA hc K' hK' hiK') (((hFL ℚ Ω l n r).2.2.2 K').2.1 hF)).2 (((hFL ℚ Ω l n r).2.2.2 K').1 hI)
    (keeps_of_pot hFL r hp) up
end UpperTheory.V.Z.Win
theorem UpperTheory.V.Z.Win.aAcross2' :
    _root_.UpperTheory.V.Z.Win.AAcross2Alt := by
  intro hP hR K Ω _ _ _ _ _ _ _ hK l _ ι n hn r hp hc hA ⟨θ, hθ, hd⟩ hI hF hirr hW K' _ _ _ inst _ _ hK' hirr'
  obtain rfl : inst = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  have hFL := UpperTheory.V.Z.Win.flagLaws
  have hUD := _root_.UpperTheory.V.Z.Win.aUpDown_alt
  obtain ⟨K'', _, _, _, _, _, hK'', -, h1, h2⟩ := UpperTheory.V.Z.Win.thirdSplit K K' Ω hK hK' l n r hirr hirr'
  have h3 := UpperTheory.V.Z.Win.step hFL hUD hP hR K K'' Ω hK hK'' l ι n hn r hp hc hA θ hθ hd hI hF h1 hW
  rw [inf_comm] at h2
  exact UpperTheory.V.Z.Win.step hFL hUD hP hR K'' K' Ω hK'' hK' l ι n hn r hp hc hA θ hθ hd hI hF h2 h3
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HdEx
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
theorem UpperTheory.V.Hi.nonempty_unitaryHeckeData :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ Λ : LamObj r, Nonempty (_root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ) := by
  intro P l _ L Ω _ _ _ _ _ _ s n hn V Q c r ι Λ
  obtain ⟨m, τ₀, hτ⟩ := _root_.UpperTheory.V.Hi.exists_integral_type_for_residual_rep P l L Ω s n hn V Q c r ι
  obtain ⟨θ, hθ, hw⟩ := _root_.UpperTheory.V.Hi.exists_theta_is_weight_of_lam_obj P.litN l L Ω s n hn V Q c m τ₀ r Λ
  obtain ⟨a, ha⟩ := _root_.UpperTheory.V.Hi.exists_is_res_of_residual_rep_and_type P.litN l L Ω s n hn V Q c m τ₀ r
  exact ⟨⟨m, τ₀, hτ, θ, hθ, hw, a, ha⟩⟩
end
end

