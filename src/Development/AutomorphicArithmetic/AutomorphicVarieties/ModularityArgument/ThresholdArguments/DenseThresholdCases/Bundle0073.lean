module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ExistsHeckeIdeal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GuWrap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.UnramifiedTwists.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.CompatTOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DualOfWeights
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0032
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0026
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0027
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BciNarrowSwap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0039
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0028
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.Narrow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.OddAOfUnl
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0047
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0043
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0020
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0040
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0019
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.GaloisRepExistsTotallyRealGL2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.ExtraV
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0041

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.JEnd1W
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
open UpperTheory.GalN.V
theorem UpperTheory.V.Hi.arithmeticPointDecomposition_of_isJ :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ) (K : (hset Q R.τ₀).Lev), V.S' = s.S → ∀ J : Ideal B.B, R.IsJ B K J → ArithmeticPointDecomposition B ι J := by
  intro H l _ L Ω _ _ _ _ _ _ s n hn V Q c r ι B Λ R K _ J hJ
  have hpr : Function.Surjective V.pr := fun g => by
    obtain ⟨τ, hτ⟩ : ∃ τ, toGS Ω V.S' τ = g.1 := QuotientGroup.mk_surjective g.1
    obtain ⟨σ, rfl⟩ := (V.hη τ).1 (by rw [hτ]; exact g.2)
    exact ⟨σ, Subtype.ext hτ⟩
  have hunr : ∀ w : HeightOneSpectrum (𝓞 L),
      Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal := by
    intro w
    have h := GlobalTheory.RayFromArtin.unramIn_of_ine (K := Lp L) (Ω := Ω) L
      (v := w.under (𝓞 (Lp L))) fun A hA σ hσ => by
        obtain ⟨g, rfl⟩ := s.unr A _ hA hσ
        ext x
        apply (algebraMap L Ω).injective
        exact (AlgEquiv.restrictNormal_commutes (W.resP L Ω g) L x).trans (g.commutes x)
    have hbot : w.asIdeal.inertia Gal(L/Lp L) = ⊥ := by
      rw [eq_bot_iff]
      intro τ hτ
      exact h τ ⟨w.asIdeal, w.isPrime, ⟨rfl⟩, hτ⟩
    have he := UpperTheory.V.CF.ineCard.1 (Lp L) L w
    rw [hbot, Subgroup.card_bot] at he
    exact Ideal.ramificationIdx_eq_one_iff.1 he.symm
  refine fun x h hx ha => ?_
  · obtain ⟨lam, ρ, hc, hs, hP, hr⟩ := _root_.hecke_ideal_end H hn hJ x h hx ha
    have hc' : Continuous (ρ.comp V.pr) := hc.comp (V.pr_cont W.continuous_resP)
    have hs' : Formalism.MainNotions.N.IsSSRep (ρ.comp V.pr) := by
      intro M hM
      obtain ⟨M', hM', hcompl⟩ := hs M (fun g => by
        obtain ⟨g', rfl⟩ := hpr g
        exact hM g')
      exact ⟨M', fun g => hM' (V.pr g), hcompl⟩
    obtain ⟨σ, hσ, hlg, -⟩ := hP.aut
    exact ⟨_, hc', hs', hr,
      _root_.UpperTheory.V.Z.Win.Gu.endShape'_alt H L Ω hunr l s.odd ι n hn σ hσ _ hc' hs' hlg⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.JPTRow
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
open UpperTheory.GalN.V UpperTheory.V.Z.Win UpperTheory.V.Z.Desc.W UpperTheory.Zero.LLC
theorem UpperTheory.V.Z.Desc.W.same_of_prints_of_rT (P : _root_.UpperTheory.V.Af.Hypotheses') (hR : RowT) : Same :=
  _root_.UpperTheory.V.Z.Desc.W.same_of_statement P (_root_.UpperTheory.BaseChangeIdentities.bcSpeh_alt (_root_.UpperTheory.BaseChangeIdentities.bridge P.litN.aut.bc P.litN.loc.bern)) satTw (sumAEOf satTw (_root_.UpperTheory.V.Z.Desc.W.galAEOf_alt P hR)) _root_.UpperTheory.V.Z.Desc.W.splitSat_alt onePart
theorem UpperTheory.V.Z.Desc.W.point_property_of_isJ_arith_rep_autCsd : RowT →
    _root_.UpperTheory.V.Af.HypothesesH' → Z.Desc.DescWeak → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ) (K : (hset Q R.τ₀).Lev), V.S' = s.S → ∀ J : Ideal B.B, R.IsJ B K J →
    ∀ (x : B.Pt) (h : s.Wt n) (ρ : G L Ω →* GL (Fin n) (Qbar l)), 2 ≤ n → n ≤ 4 → x.Arith h →
    x.IsRep ρ → Continuous ρ → IsAutCsdA ι ρ → (∀ g ∈ Ine (F := L) (s.A s.v0), ρ g = 1) →
    (∀ v : Vl l L, W.HasFlag (ρ.comp (Dec (F := L) (s.A v)).subtype) (x.psi v) ∧
      ∀ i j, x.psi v i ≠ x.psi v j * (cycBar L Ω l).comp (Dec (F := L) (s.A v)).subtype) →
    J ≤ RingHom.ker x :=
  fun hR PH => _root_.UpperTheory.V.Z.Desc.W.jPT_of_alt recTExists (compatTOf hR plainRec) plainRec (_root_.UpperTheory.V.Z.Desc.W.same_of_prints_of_rT PH.toClassicalTheorems hR) _root_.UpperTheory.V.Z.Desc.W.sphT_alt _root_.UpperTheory.V.Z.Desc.W.pseudo_local_langlands_descent unlOf PH
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.KeepLevel
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Lev UpperTheory.V.Z.Win
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Keep
theorem levelCore_alt (P : _root_.UpperTheory.V.Af.Hypotheses') (K : Type) [Field K] [NumberField K] [IsCMField K] (n : ℕ) (hn : 2 ≤ n) (m : Fin n → ℤ)
    (M : ℕ) (hM : 1 ≤ M) (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ)
    (r : G K Ω →* GL (Fin n) (Qbar l)) (π : CuspSub K n) (hL : LevelF l M m r)
    (hU : ∀ w : HeightOneSpectrum (𝓞 K), ((l : ℕ) : 𝓞 K) ∈ w.asIdeal → Unl1 r w ∨ PotUnl r w) (hW : WitA ι r)
    (hreg : (CG.mk π).IsRegAlg) (hpol : ∃ χ, GlobalTheory.ContraPair.PolarizedPair π χ) (ha : AttC ι r π) :
    (∀ τ, π.HasInfChar τ (infOf m)) ∧ HasFixed π.finPart (KLev K n M) ∧
      ∀ w : HeightOneSpectrum (𝓞 K), (l : 𝓞 K) ∉ w.asIdeal → ∀ B, (CG.mk π).HasSat w B → FrobEig ι r w (algSat n (normV w) B) := by
  obtain ⟨HT, hwt, hC⟩ := compatT (_root_.UpperTheory.Gal.SV.rowOf' P.litN.aut.gal) K Ω l ι n (by omega) r π hL.cont hreg hpol ha
  have hw' : ∀ w : HeightOneSpectrum (𝓞 K), ((l : ℕ) : 𝓞 K) ∉ w.asIdeal ∨ Unl1 r w ∨ PotUnl r w := fun w =>
    (em _).elim (fun e => Or.inr (hU w e)) Or.inl
  refine ⟨fun φ => ?_, ?_, fun w hw B hB => ?_⟩
  · let τ : K →+* Qbar l := ι.symm.toRingHom.comp φ
    have hφ : ι.toRingHom.comp τ = φ := RingHom.ext fun x => ι.apply_symm_apply _
    obtain ⟨w, hw, hτ⟩ := GlobalTheory.GalFirstClause.existsIsInduced l K Ω τ
    obtain ⟨A, hA, κ, hκ⟩ := hL.above w hw
    obtain ⟨O, _, _, _, Bw, hj⟩ := exists_bridge (l := l) hA hw
    obtain ⟨τ', hτ'⟩ := hτ A hA O Bw hj
    obtain ⟨⟨σ, hσ⟩, -⟩ := _root_.UpperTheory.V.Af.local_comp_complex_of_printed_results P K n π w
    obtain ⟨rc, hrc⟩ := P.exists_reciprocity_dense hA
    have g := guard_of plainRec hreg ha hW (hw' w) (_root_.UpperTheory.V.Z.Desc.W.isRecT_of_isRecT P hrc) hσ
    have hJ := _root_.UpperTheory.V.Af.jumps_above_of_printed_results P K Ω l hl n M hM m r hL.cont w A hA O Bw hj κ hκ τ _
      (((hC w σ hσ).2 g.1 A hA O Bw hj).2 τ _ τ' hτ')
    have hw := hwt τ
    rw [hJ, hφ] at hw
    have hinf : (CG.mk π).infChar φ = infOf m := by
      have h := congrArg (Multiset.map fun z : ℂ => ((n : ℂ) - 1) / 2 - z) hw
      simp only [Multiset.map_map, Function.comp_def, sub_sub_cancel, Multiset.map_id'] at h
      rw [← h, infOf]
      exact Multiset.map_congr rfl fun i _ => by push_cast; ring
    rw [← hinf]
    exact ParLaws.hasInfChar_infChar (CG.mk π) φ
  · refine _root_.UpperTheory.V.Af.globFixed_alt P K n M hM _ π.finPart π.isSmooth_finPart fun w => ?_
    obtain ⟨⟨σ, hσ⟩, hi⟩ := _root_.UpperTheory.V.Af.local_comp_complex_of_printed_results P K n π w
    refine ⟨σ, hi σ hσ, ?_⟩
    by_cases hw : ((l : ℕ) : 𝓞 K) ∈ w.asIdeal
    · obtain ⟨A, hA, κ, hκ⟩ := hL.above w hw
      obtain ⟨O, _, _, _, Bw, hj⟩ := exists_bridge (l := l) hA hw
      obtain ⟨rc, hrc⟩ := P.exists_reciprocity_dense hA
      have g := guard_of plainRec hreg ha hW (hw' w) (_root_.UpperTheory.V.Z.Desc.W.isRecT_of_isRecT P hrc) hσ
      obtain ⟨hp, he⟩ := ((hC w σ hσ).1 A hA rc (_root_.UpperTheory.V.Z.Desc.W.isRecT_of_isRecT P hrc)).2 O Bw hj g.2
      refine _root_.UpperTheory.V.Lev.fixedSs_of_prints P K Ω l ι n M hM m r hL.cont w A hA O Bw hj κ hκ hp rc hrc σ (fun _ s => by rw [he]) ?_
      by_cases hlM : l ∣ M
      · exact Or.inl hlM
      have hM' : (M : 𝓞 K) ∉ w.asIdeal := by
        intro h
        obtain ⟨a, b, e⟩ : IsCoprime (l : 𝓞 K) (M : 𝓞 K) :=
          Nat.Coprime.cast ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hlM)
        exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
          (e ▸ w.asIdeal.add_mem (w.asIdeal.mul_mem_left a hw) (w.asIdeal.mul_mem_left b h)))
      refine Or.inr (Or.inr fun _ => ?_)
      obtain ⟨μ, m1, m2, -⟩ := flagPol K Ω l ι n M hM m r hL.cont w A hA O Bw hj κ hκ hp
      refine sphV (_root_.UpperTheory.V.Z.Win.toV' hrc) σ g.2.2 n fun s => ?_
      rw [← he, m1]
      simp only [fun i => m2 i s (UpperTheory.inertia_fixes_roots_of_unity_prime_to_residue_char K Ω w A hA M hM' s s.2), Units.val_one, C_1,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    · obtain ⟨A, hA, χ, h1, h2⟩ := hL.away w hw
      obtain ⟨rc, hrc⟩ := P.exists_reciprocity_dense hA
      have g := guard_of plainRec hreg ha hW (hw' w) (_root_.UpperTheory.V.Z.Desc.W.isRecT_of_isRecT P hrc) hσ
      exact _root_.UpperTheory.V.Z.Win.T2.local_fixed_vectors_statement P K Ω n M hM w A hA rc hrc σ
        (_root_.UpperTheory.V.Af.weil_deligne_away_of_printed_results P K Ω l ι n M hM r hL.cont w hw A hA χ h1 h2 _
          ((((hC w σ hσ).1 A hA rc (_root_.UpperTheory.V.Z.Desc.W.isRecT_of_isRecT P hrc)).1 hw).isWDOf g.2))
  · obtain ⟨⟨σ, hσ⟩, hi⟩ := _root_.UpperTheory.V.Af.local_comp_complex_of_printed_results P K n π w
    exact _root_.UpperTheory.V.Z.Desc.W.satFrobT_alt P K Ω l ι n r hL.cont w hw σ B (((_root_.UpperTheory.V.Af.satake_local_of_printed_results P K n w σ).2 _ π.finPart (hi σ hσ) B).1 hB)
      fun A h rc hrc => ((hC w σ hσ).1 A h rc hrc).1 hw
theorem levelPA_alt (P : _root_.UpperTheory.V.Af.Hypotheses') : LevelPA := by
  intro K _ _ _ _ n hn m _ M hM l _ hl Ω _ _ _ ι r π hL hs hW hreg hpol ha
  have h := _root_.UpperTheory.V.Keep.levelCore_alt P K n hn m M hM l hl Ω ι r π hL (fun w hw => hs.elim (fun a => Or.inr (a.2 w hw)) fun hg => by
    obtain ⟨A, hA, κ, hκ⟩ := hL.above w hw
    have hu := unlGap K Ω l n M hM m r w hw A hA κ hκ hg
    obtain ⟨χ, -, h2, -⟩ := hκ
    exact Or.inl (A4.unlOfOne K Ω l n r w A hA κ h2 hu)) hW hreg hpol ha
  exact ⟨⟨h.1, hpol, h.2.1⟩, h.2.2⟩
section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {n : ℕ}
variable [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {r : G F Ω →* GL (Fin n) (Qbar l)}
end
theorem levelKA_alt (P : _root_.UpperTheory.V.Af.Hypotheses') : LevelKA := by
  intro K _ _ _ n hn m _ M hM l _ hl Ω _ _ _ ι r π hL hU hW hreg hd ha
  have hpol : GlobalTheory.ContraPair.PolarizedPair π (quadChar K ^ n) :=
    ⟨fun v => by rw [locInf_pow, quadChar_locInf], by
      rw [map_pow, compNorm_quadChar, one_pow]; exact (GlobalTheory.ContraPair.dualIsConjBy_one π).2 hd⟩
  have h := _root_.UpperTheory.V.Keep.levelCore_alt P K n hn m M hM l hl Ω ι r π (LevelF.of_level hL) hU hW hreg ⟨_, hpol⟩ ha
  exact ⟨⟨h.1, hd, h.2.1⟩, h.2.2⟩
end UpperTheory.V.Keep
end
end
end

