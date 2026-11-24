module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GuWrap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.SpehInfRankOneEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.SpehInfLenOne
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.RealAway
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0048
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0040
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0025
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.UnitaryTorusDescent.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0055
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.WeilCharpolySupport.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TCompEx

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BcOf
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Af UpperTheory.V.Z.Desc.P
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem UpperTheory.V.Z.Desc.P.dense_threshold_bc_of_prop : _root_.UpperTheory.V.Z.J.D.BcOfAlt := by
  intro H E Ω _ _ _ _ _ _ hE l _ hl ι n hn σ hσ R hRc hRi hR
  obtain ⟨r, HT, hc, hs, -, -, hL, -, hQ⟩ := _root_.UpperTheory.V.Z.Win.Gu.galUnitaryT_of_printsH H E Ω hE l hl ι n hn σ hσ
  have hss : Formalism.MainNotions.N.IsSSRep R := by
    intro M hM
    rcases hRi.2.2 M le_top hM with rfl | rfl
    · exact ⟨⊤, hRi.2.1, isCompl_bot_top⟩
    · refine ⟨⊥, fun g v hv => ?_, isCompl_top_bot⟩
      rw [(Submodule.mem_bot _).1 hv]
      simp
  have hunram : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, IsUnramU σ w := by
    obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hσ.ne_bot
    let L : Subgroup (finU (E := E) (n := n)) :=
      { carrier := {k | RU E n k φ = φ}
        one_mem' := by simp
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_ofPred_eq] at *
          rw [Subgroup.coe_mul, map_mul, mul_apply_eq_comp, hb, ha]
        inv_mem' := by
          intro a ha
          simp only [Set.mem_ofPred_eq] at *
          conv_lhs => rw [← ha]
          rw [← mul_apply_eq_comp, ← map_mul, Subgroup.coe_inv, inv_mul_cancel,
            map_one, one_apply_eq_self] }
    have hLo : IsOpen (L : Set (finU (E := E) (n := n))) := (hσ.aut φ hφ).level
    filter_upwards [GlobalTheory.T.eventually_localIntegralPoints_mem_openSubgroup_definiteUnitary
      E n L hLo] with w hw
    exact ⟨φ, hφ, hφ0, fun x hx hxK => hw x hx hxK hx.1⟩
  have hAway : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, (l : 𝓞 E) ∉ w.asIdeal := by
    have h0 : Ideal.span {(l : 𝓞 E)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast (Fact.out : l.Prime).ne_zero
    exact (Ideal.finite_factors h0).subset fun w hw => Ideal.dvd_span_singleton.mpr (not_not.1 hw)
  have hAgree : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite,
      IsSplitAt w → ∃ B, FrobEig ι R w B ∧ FrobEig ι r w B := by
    filter_upwards [hR, hAway, hunram] with w h1 hw hu hsp
    obtain ⟨τ, -, h2, h3⟩ := GlobalTheory.DefU.exists_locComp_split E n ⟨σ, hσ⟩ w hsp
    obtain ⟨v, hv, h0⟩ := (Submodule.ne_bot_iff _).1 (h3.1 hu)
    obtain ⟨b, hb⟩ := (_root_.UpperTheory.V.Af.satake_local_of_printed_results H.toClassicalTheorems E n w τ).1 ⟨v, h0, fun u hu => by simpa using hv ⟨u, hu⟩⟩
    have k : _root_.UpperTheory.V.Z.Win.LocGlobT ι r w τ := (hL w hsp τ h2).1
    exact ⟨_, _root_.UpperTheory.V.Z.Desc.W.satFrobT_alt H.toClassicalTheorems E Ω l ι n R hRc w hw τ b hb (_root_.UpperTheory.V.Z.Desc.P.lgAwayT (h1 hsp τ h2) hw),
      _root_.UpperTheory.V.Z.Desc.W.satFrobT_alt H.toClassicalTheorems E Ω l ι n r hc w hw τ b hb (_root_.UpperTheory.V.Z.Desc.P.lgAwayT k hw)⟩
  have hiso : RepIso R r := by
    have hChar : ∀ g : G E Ω, (R g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly =
        (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly := by
      intro g
      ext i
      have hRcoeff : Continuous fun g : G E Ω =>
          (R g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
        (GlobalTheory.LocBound.continuous_coeff_charpoly n i).comp
          (Units.continuous_val.comp (hRc.comp continuous_inv))
      have hrcoeff : Continuous fun g : G E Ω =>
          (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
        (GlobalTheory.LocBound.continuous_coeff_charpoly n i).comp
          (Units.continuous_val.comp (hc.comp continuous_inv))
      refine congrFun (GlobalTheory.Published.chebotarevDegreeOne'.eq_of_frob
        (Filter.eventually_cofinite.1 hAgree) hRcoeff hrcoeff ?_) g
      intro w hw hd A hA s hFrob
      have hSplit := UpperTheory.isSplitAt_of_unramified_of_inertiaDeg_eq_one E w (hE w) hd
      obtain ⟨B, hB, hB'⟩ := not_not.1 hw hSplit
      have h := ((hB A hA).2 s hFrob).trans ((hB' A hA).2 s hFrob).symm
      have h' := Polynomial.map_injective ι.toRingHom ι.injective h
      rw [h']
    obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix R r hss hs
      (fun g => by simpa using hChar g⁻¹)
    exact ⟨P⁻¹, fun g => by rw [hP g, inv_inv]⟩
  have hirr : IsIrr r := by
    obtain ⟨P, hP⟩ := hiso
    refine ⟨hRi.1, fun _ _ _ => Submodule.mem_top, fun M _ hM => ?_⟩
    let T : (Fin n → Qbar l) ≃ₗ[Qbar l] (Fin n → Qbar l) :=
      (Matrix.GeneralLinearGroup.toLin P).toLinearEquiv
    have hT : ∀ v, T v = (P : Matrix (Fin n) (Fin n) (Qbar l)).mulVec v := fun v => rfl
    have hInv : Formalism.MainNotions.N.IsInv R (M.comap T.toLinearMap) := by
      intro g v hv
      have hComm : T ((R g : Matrix (Fin n) (Fin n) (Qbar l)).mulVec v) =
          (r g : Matrix (Fin n) (Fin n) (Qbar l)).mulVec (T v) := by
        rw [hT, hT, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hP g]
        simp [Matrix.mul_assoc]
      show T _ ∈ M
      rw [hComm]
      exact hM g _ hv
    have hMap := (Submodule.map_comap_eq_of_surjective T.surjective M).symm
    rcases hRi.2.2 _ le_top hInv with h | h
    · left
      rw [hMap, h, Submodule.map_bot]
    · right
      rw [hMap, h, Submodule.map_top, LinearMap.range_eq_top.2 T.surjective]
  obtain ⟨π, h1, h2, -, h4, h5, h6⟩ := hQ hirr
  refine ⟨π, h1, h2, ?_, h4, h5⟩
  filter_upwards [(_root_.UpperTheory.satake_galois_link_of_printed_hida H E n π).2] with w ⟨B, hB⟩ hsp
  obtain ⟨τ, hτ⟩ := (_root_.UpperTheory.V.Af.local_comp_complex_of_printed_results H.toClassicalTheorems E n π w).1
  exact ⟨τ, B, h6 w hsp τ hτ, ((_root_.UpperTheory.satake_galois_link_of_printed_hida H E n π).1 w τ hτ B).1 hB, hB⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Link2
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
open UpperTheory.V.Z UpperTheory.V.Z.Ord UpperTheory.Gal.projectedFormsSystemPart UpperTheory.GalN.V
namespace UpperTheory.Gal.projectedFormsSystemPart
section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)} {w : Plc F} {τ : SmIrr (GLw n w)} {B : Multiset ℂˣ}
end
theorem link2_alt (H : _root_.UpperTheory.V.Af.HypothesesH') (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (hE : ∀ w : Plc E, Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) (l : ℕ) [Fact l.Prime] (hl2 : l ≠ 2)
    (ι : Qbar l ≃+* ℂ) (n : ℕ) (hn : 1 ≤ n) (σ : Submodule ℂ (UA E n → ℂ)) (hσ : IsAutRepU σ)
    (ρ : G E Ω →* GL (Fin n) (Qbar l)) (hρc : Continuous ρ) (hρi : Af.IsIrr ρ)
    (hρF : ∀ᶠ w : Plc E in Filter.cofinite, IsSplitAt w → ∀ τ : SmIrr (GLw n w),
      IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ → ∀ B, GlobalTheory.LFun.HasSatGL w τ.ρ B →
        Af.FrobEig ι ρ w (Af.algSat n (normV w) B)) :
    ∃ π : CuspSub E n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ Af.AttC ι ρ π ∧
      (∀ w, IsUnramU σ w → ∃ B, (CG.mk π).HasSat w B) ∧ ∀ w, IsSplitAt w → ∀ τ : SmIrr (GLw n w),
        π.IsLocComp w τ ↔ IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ := by
  obtain ⟨r, HT, hc, hs, -, -, hLG, -, hcusp⟩ := _root_.UpperTheory.V.Z.Win.Gu.galUnitaryT_of_printsH H E Ω hE l hl2 ι n hn σ hσ
  have hoff : ∀ᶠ w : Plc E in Filter.cofinite, (l : 𝓞 E) ∉ w.asIdeal := by
    have h0 : Ideal.span {(l : 𝓞 E)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast (Fact.out : l.Prime).ne_zero
    exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)
  have hunram : ∀ᶠ w : Plc E in Filter.cofinite, IsUnramU σ w := by
    obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hσ.ne_bot
    let L : Subgroup (finU (E := E) (n := n)) :=
      { carrier := {k | RU E n k φ = φ}
        one_mem' := by simp
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_ofPred_eq] at *
          rw [Subgroup.coe_mul, map_mul, mul_apply_eq_comp, hb, ha]
        inv_mem' := by
          intro a ha
          simp only [Set.mem_ofPred_eq] at *
          conv_lhs => rw [← ha]
          rw [← mul_apply_eq_comp, ← map_mul, Subgroup.coe_inv, inv_mul_cancel,
            map_one, one_apply_eq_self] }
    have hLo : IsOpen (L : Set (finU (E := E) (n := n))) := (hσ.aut φ hφ).level
    filter_upwards [GlobalTheory.T.eventually_localIntegralPoints_mem_openSubgroup_definiteUnitary E n L hLo] with w hw
    exact ⟨φ, hφ, hφ0, fun x hx hxK => hw x hx hxK hx.1⟩
  have hagree : ∀ᶠ w : Plc E in Filter.cofinite, w.asIdeal.inertiaDeg ℤ = 1 →
      ∃ B, Af.FrobEig ι r w B ∧ Af.FrobEig ι ρ w B := by
    filter_upwards [hoff, hunram, hρF] with w hl hu hw hd
    have hsp := UpperTheory.isSplitAt_of_unramified_of_inertiaDeg_eq_one E w (hE w) hd
    obtain ⟨τ, hτ⟩ := (GlobalTheory.SplitComp.exists_comp_and_unique E n σ hσ w hsp).1
    obtain ⟨x, hx, h0⟩ := (Submodule.ne_bot_iff _).1 (GlobalTheory.SphBC.isSpherical_of_isCompAlong_split hσ hsp τ.ρ hτ hu)
    obtain ⟨B, hB⟩ := (_root_.UpperTheory.V.Af.satake_local_of_printed_results H.toClassicalTheorems E n w τ).1 ⟨x, h0, GlobalTheory.LGrp.mem_fixed.1 hx⟩
    exact ⟨_, _root_.UpperTheory.Gal.projectedFormsSystemPart.frobLG'_alt H.toClassicalTheorems hc hl hB (hLG w hsp τ hτ).1, hw hsp τ hτ B hB⟩
  have hρss : IsSSRep ρ := fun M hM => by
    rcases hρi.2.2 M le_top hM with rfl | rfl
    · exact ⟨⊤, hρi.2.1, isCompl_bot_top⟩
    · refine ⟨⊥, fun g v hv => ?_, isCompl_top_bot⟩
      rw [(Submodule.mem_bot _).1 hv]
      simp
  have e : Af.RepIso r ρ := by
    have hchar := UpperTheory.V.Af.Es.charpoly_eq_prod ι (I := Unit) (a := fun _ => n)
      r (fun _ => ρ) hc (fun _ => hρc) (hagree.mono fun w h hd => by
        obtain ⟨B, h1, h2⟩ := h hd
        exact ⟨fun _ => B, by simpa using h1, fun _ => h2⟩)
    obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix
      r ρ hs hρss (fun g => by simpa using hchar g)
    exact ⟨P⁻¹, fun g => by rw [hP g, inv_inv]⟩
  have hri : Af.IsIrr r := by
    obtain ⟨P, hP⟩ := Af.RepIso.symm' e
    refine ⟨hρi.1, fun _ _ _ => Submodule.mem_top, fun M _ hM => ?_⟩
    let T := (Matrix.GeneralLinearGroup.toLin P).toLinearEquiv
    have hT : ∀ v, T v = (P : Matrix (Fin n) (Fin n) (Qbar l)).mulVec v := fun v => rfl
    have hi : IsInv ρ (M.comap T.toLinearMap) := fun g v hv => by
      have h1 := hM g _ hv
      change (r g : Matrix (Fin n) (Fin n) (Qbar l)).mulVec (T v) ∈ M at h1
      change T _ ∈ M
      have e1 : P * ρ g = r g * P := by rw [hP g, inv_mul_cancel_right]
      rw [hT, Matrix.mulVec_mulVec, ← Units.val_mul, e1, Units.val_mul,
        ← Matrix.mulVec_mulVec, ← hT]
      exact h1
    have hm := (Submodule.map_comap_eq_of_surjective T.surjective M).symm
    rcases hρi.2.2 _ le_top hi with h0 | h1
    · left
      rw [hm, h0, Submodule.map_bot]
    · right
      rw [hm, h1, Submodule.map_top, LinearMap.range_eq_top.2 T.surjective]
  obtain ⟨π, p1, p2, p3, -, p4, p5⟩ := hcusp hri
  refine ⟨π, p1, p2, ⟨hρss, p3.2.mono fun w ⟨b, hb, hf⟩ => ⟨b, hb, hf.of_iso e⟩⟩, p4, fun w hw τ => ⟨p5 w hw τ, fun hτ => ?_⟩⟩
  obtain ⟨τ', hτ'⟩ := (_root_.UpperTheory.V.Af.local_comp_complex_of_printed_results H.toClassicalTheorems E n π w).1
  exact (GlobalTheory.BCT.isLocComp_iff_equiv hτ' τ).2 (UpperTheory.building_component_uniqueness E n σ hσ w hw _ _ _ _ hτ (p5 w hw τ' hτ'))
end UpperTheory.Gal.projectedFormsSystemPart
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TGalExW
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
theorem UpperTheory.V.Z.Sym.W.galois_exists_w_statement :
    _root_.UpperTheory.V.Z.Sym.W.GalExWAlt := by
  intro P L Ω _ _ _ _ _ _ l _ ι hl hE n hn σ hσ
  obtain ⟨r, HT, hc, hs, -, -, hLG, hp, hi⟩ := P.gal L Ω hE l hl ι n hn σ hσ
  refine ⟨r, ⟨hc, _root_.UpperTheory.V.Z.Sym.Al.exists_local_component_at_split_of_unitary_aut P.af.litN L hE n hn σ hσ,
    fun w hw τ hτ => (hLG w hw τ hτ).1, hp⟩, fun h => ?_⟩
  obtain ⟨π, h1, h2, h3, -, h4, h5⟩ := hi h
  exact ⟨π, h1, h2, h3, h4, h5⟩
end
end

