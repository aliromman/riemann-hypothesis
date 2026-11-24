module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0044
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0061
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HeckeOperatorPreservesPart
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0051
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.CharOfScalar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0039
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0043
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0048
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OrdPartPt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0056
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0058
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0041
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.RankTwoDescentSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgOfCyc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0028
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0031
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0059
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0022

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OrdCoreH
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem UpperTheory.V.Z.Ord.core_hecke_of_automorphic_hecke_dense_weight :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ) (P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop), H.AutomorphicHeckeSet ι P →
    ∀ lam0 ∈ H.admitted, H.DenseWt θ lam0 → ∀ (a : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))] [Alg.IsCO c.O (H.TK θ a K)], ∀ (D : W.GDet n (H.TK θ a K) H.Gq) (ψ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* (H.TK θ a K)ˣ), H.IsUniv θ a K (maximalIdeal _) D ψ →
    H.Out θ a K P (maximalIdeal _) D ψ := by
  intro hL L Ω _ _ _ _ _ l _ n c H hA A _ _ _ θ hθ ι P hP _ _ _ a K _ _ D ψ hU
  refine ⟨hU, _root_.UpperTheory.V.Hi.eq_zero_of_vanish_at_good_points_dense_weight hL L Ω l n c H hA A θ hθ ι P hP a K, fun lam hlam y hy => ?_⟩
  let x : A →ₐ[c.O] Qbar l := y.comp (IsScalarTower.toAlgHom c.O A (H.TK θ a K))
  have hx : y.toRingHom.comp (algebraMap A _) = x.toRingHom := rfl
  rw [hx] at hy ⊢
  obtain ⟨d, ξ, c0, sp, hsp⟩ := UpperTheory.V.Hi.spec L Ω l n c H hA A θ hθ ι x lam hy
  obtain ⟨-, -, -, -, -, hpt, -⟩ :=
    _root_.UpperTheory.V.Hi.partAct0_alt hL L Ω l n c H hA A θ hθ ι P hP x lam d ξ c0 sp hsp hlam a K _ rfl
  obtain ⟨Y, F, e, hY, he, hF0, hF, hop⟩ := hpt y hx
  obtain ⟨hD, hch⟩ := _root_.UpperTheory.V.Hi.core_eigen_of_weight_char_hecke_level hL L Ω l n c H hA A θ hθ ι a K D ψ hU y lam d ξ Y F hF.1 hF0
    fun w j => hop _
  refine ⟨Y.r, Y.cont, Y.ss, hY, hD, fun hg v => ?_⟩
  obtain ⟨ω, hsm, hPS, hinv, hU'⟩ := _root_.UpperTheory.V.Hi.goodScalB_alt hL L Ω l n c H hA A θ hθ ι x lam d ξ c0 sp hsp hg Y K e he
    fun h0 => hF0 ((Submodule.mem_bot ℂ).1 (h0 ▸ hF))
  have hO := hch v (ω v) (hsm v) (hinv v) fun j =>
    smul_left_injective ℂ hF0 ((hop (.inr (v, j))).symm.trans ((hU' v j).2 F hF))
  obtain ⟨rc, hrc⟩ := _root_.UpperTheory.V.Z.Win.exRec'_alt hL (H.ovr v)
  obtain ⟨φ⟩ := hPS v
  have hpol := (_root_.UpperTheory.V.Z.Win.T2.psRec_alt hL L Ω n (H.Sl v) (H.pl v) (H.ovr v) (H.art v) (hA.art_spec v) rc hrc (Y.σl v) (ω v)
    (hsm v)).1 (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)
  have hdist : ∀ i j, i ≠ j → ∃ u : Uo ((H.Sl v).adicCompletion L), ω v i u ≠ ω v j u := fun i j hij => by
    obtain ⟨u, hu⟩ := hg.2.2 v i j hij
    refine ⟨u, fun h0 => hu (ι.injective (mul_left_cancel₀ (ω v j u).ne_zero ?_))⟩
    rw [hinv v j u, ← h0, hinv v i u]
  have hdr := _root_.UpperTheory.V.Z.Ord.useAtL' (Y.atL v) (ω v) (hsm v) hdist ⟨φ⟩ rc hrc ((UpperTheory.V.Lev.ssCalc L Ω _ _ (H.ovr v)).1 n _ (fun j => (ω v j).comp (H.art v)) hpol)
  rw [funext hpol] at hdr
  refine _root_.UpperTheory.V.Loc.ordFlag_alt hL L Ω l hA.odd ι n (H.Sl v) (hA.Sl_over v) (H.pl v) (H.ovr v) (H.art v) (hA.art_spec v)
    _ (Y.cont.comp (hA.prj_cont.comp continuous_subtype_val)) (htW lam) (fun τ i j hij => ?_) (ω v) _ hO
    (fun i j hij => ?_) hdr
  · have h1 := (lam τ).anti (Fin.rev_le_rev.2 hij.le)
    have h2 : (i : ℕ) < j := hij
    simp only [htW, lowW]
    omega
  · obtain ⟨u, hu⟩ := hg.2.2 v i j hij
    refine ⟨u, fun h0 => hu (ι.injective (mul_left_cancel₀ (ω v j u).ne_zero ?_))⟩
    rw [hinv v j u, ← h0, hinv v i u]
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OrdCoreOrd
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z UpperTheory.V.Z.Ord
set_option synthInstance.maxHeartbeats 200000
theorem UpperTheory.V.Z.Ord.core_ordinary_of_literal_automorphy_n :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → _root_.UpperTheory.V.Z.Ord.CoreOrdAlt := by
  intro hL L Ω _ _ _ _ _ l _ n c H hA A _ _ _ θ hθ ι P hP a K _ _ D ψ hU lam hlam y hy
  let x : A →ₐ[c.O] Qbar l := y.comp (IsScalarTower.toAlgHom c.O A (H.TK θ a K))
  have hx : y.toRingHom.comp (algebraMap A _) = x.toRingHom := rfl
  rw [hx] at hy
  obtain ⟨d, ξ, c0, sp, hsp⟩ := UpperTheory.V.Hi.spec L Ω l n c H hA A θ hθ ι x lam hy
  obtain ⟨Y, F, hY, hF0, hF, hop⟩ :=
    _root_.UpperTheory.V.Z.Ord.ordinary_pt_of_literal_automorphy_n hL L Ω l n c H hA A θ hθ ι P hP x lam d ξ c0 sp hsp hlam a K y hx
  obtain ⟨hD, hch⟩ := _root_.UpperTheory.V.Hi.core_eigen_of_weight_char_hecke_level hL L Ω l n c H hA A θ hθ ι a K D ψ hU y lam d ξ Y F hF.1 hF0
    fun w j => hop _
  refine ⟨d, ξ, Y, hY, hD, fun v => ?_⟩
  have hle : H.OrdAt θ ι x.toRingHom lam ξ K c0 ≤ H.ClAt θ ι x.toRingHom lam ξ K c0 := by
    unfold HSet.OrdAt
    exact iSup_le fun _ => inf_le_left
  have hC : F ∈ Y.Y ⊓ H.ClAt θ ι x.toRingHom lam ξ K c0 := ⟨hF.1, hle hF.2⟩
  have hne : ∀ j : Fin n, ι (y (H.gen θ a K (.inr (v, j)))) ≠ 0 := fun j => by
    obtain ⟨s, hs⟩ := (hA.art_spec v).surj (unif _)
    rw [← hU.ψ_unif v j s (Subgroup.inclusion (Weil_le_Dec (H.ovr v)) s) rfl hs]
    exact (map_ne_zero ι).2 ((Units.isUnit _).map y).ne_zero
  obtain ⟨ω, hsm, hPS, hinv, hb⟩ := _root_.UpperTheory.V.Z.Ord.ordinary_scalar_of_literal_automorphy_n hL L Ω l n c H hA A θ hθ ι x lam d ξ c0 sp hsp
    Y K c0 le_rfl F hC hF0 v (fun j => ι (y (H.gen θ a K (.inr (v, j))))) fun j => ⟨hne j, hop _⟩
  exact ⟨ω, hPS, hch v ω hsm hinv hb⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.RankTwoDescentSplit
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.Base UpperTheory.V.Af
open scoped Matrix
private theorem cc_ex (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] : ∃ c : G ℚ Ω, IsConjEl c := by
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  let j : Ω →ₐ[ℚ] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  letI : Algebra Ω ℂ := j.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  let τ : ℂ ≃ₐ[ℚ] ℂ := AlgEquiv.ofRingEquiv (f := starRingAut) fun x => by simp
  exact ⟨τ.restrictNormal Ω, algebraMap Ω ℂ, fun x => AlgEquiv.restrictNormal_commutes τ Ω x⟩
private theorem cc_mu {Ω : Type} [Field Ω] [CharZero Ω] {c : G ℚ Ω} (hc : IsConjEl c) {M : ℕ} (hM : 1 ≤ M) {ζ : Ω}
    (h : ζ ^ M = 1) : c ζ = ζ⁻¹ := by
  obtain ⟨j, hj⟩ := hc
  apply j.injective
  have h1 : (j ζ) ^ M = 1 := by rw [← map_pow, h, map_one]
  rw [hj, map_inv₀, Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one h1 (by omega))]
private theorem kills_cc {Ω : Type} [Field Ω] [CharZero Ω] {C : Type} [CommGroup C] {M : ℕ} (hM : 1 ≤ M) {χ : G ℚ Ω →* C}
    (hχ : KillsMu M χ) {c c' : G ℚ Ω} (hc : IsConjEl c) (hc' : IsConjEl c') : χ c = χ c' := by
  have := hχ (c⁻¹ * c') fun ζ h => by
    rw [AlgEquiv.mul_apply, cc_mu hc' hM h, ← cc_mu hc hM h]
    exact c.symm_apply_apply ζ
  rw [map_mul, map_inv, inv_mul_eq_one] at this
  exact this
private theorem kills_pow {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {C : Type} [CommGroup C] {M : ℕ} (hM : 1 ≤ M)
    {χ : G ℚ Ω →* C} (hχ : KillsMu M χ) : ∃ k : ℕ, 0 < k ∧ ∀ s, χ s ^ k = 1 := by
  haveI : NeZero M := ⟨by omega⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨μ, hμ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  refine ⟨Fintype.card (ZMod M)ˣ, Fintype.card_pos, fun s => ?_⟩
  rw [← map_pow]
  refine hχ _ fun ζ h => ?_
  have h1 := hμ.autToPow_spec ℚ (s ^ Fintype.card (ZMod M)ˣ)
  rw [map_pow, pow_card_eq_one, Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ hμ.pow_eq_one, pow_one] at h1
  obtain ⟨i, -, rfl⟩ := hμ.eq_pow_of_pow_eq_one h
  rw [map_pow, ← h1]
private theorem pair2 {k : Type} [Field k] (A : Matrix (Fin 2) (Fin 2) k) :
    Aᵀ * !![0, 1; -1, 0] * A = A.det • (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) k) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.det_fin_two] <;> ring
private theorem pairing2 {F Ω k : Type} [Field F] [Field Ω] [Algebra F Ω] [Field k] (r : G F Ω →* GL (Fin 2) k) (c : G F Ω) :
    ∃ P, IsPairing c r ((Matrix.GeneralLinearGroup.det.comp r).comp (resG F F Ω)) P := by
  let J : GL (Fin 2) k := Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; -1, 0] (by simp [Matrix.det_fin_two])
  refine ⟨J * r c⁻¹, fun s s' h => ?_⟩
  have h' : s' = c * s * c⁻¹ := h
  have e : r c⁻¹ * r s' = r s * r c⁻¹ := by rw [h', ← map_mul, ← map_mul]; congr 1; group
  have e' : (r c⁻¹).val * (r s').val = (r s).val * (r c⁻¹).val := congrArg Units.val e
  have hp : (r s).valᵀ * J.val * (r s).val = (r s).val.det • J.val := pair2 _
  have hd : (((Matrix.GeneralLinearGroup.det.comp r).comp (resG F F Ω) s : kˣ) : k) = (r s).val.det := rfl
  rw [hd, Units.val_mul, ← Matrix.smul_mul, ← hp]
  simp only [Matrix.mul_assoc, e']
private theorem tf (L Ω : Type) [Field L] [Field Ω] [Algebra L Ω] : Module.IsTorsionFree L Ω :=
  DivisionSemiring.to_moduleIsTorsionFree
attribute [local instance] tf
private theorem algClosure_up (L Ω : Type) [Field L] [CharZero L] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra L Ω] :
    IsAlgClosure L Ω :=
  ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) L⟩
open UpperTheory.V UpperTheory.V.Af in
private theorem via (P : _root_.UpperTheory.V.Af.HypothesesH') (cyc : Z.Bc.CycC) (cyc2 : Z.Bc.DescS) (hG : Z.Bc.GapTwo) (K L Ω : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsAbelianGalois ℚ L]
    (hK : Module.finrank ℚ K = 2) (hC : IsCMField K) (hL : IsCMField L) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (W : G ℚ Ω →* GL (Fin 2) (Qbar l)) (hW : Continuous W) (hirr : IsIrr (W.comp (resG ℚ L Ω))) (hpol : Sol.Pol ι W)
    (hfin : ∃ N : ℕ, 0 < N ∧ ∀ s, Matrix.GeneralLinearGroup.det (W s) ^ N = 1)
    (haut : IsAut ι (W.comp (resG ℚ L Ω))) : IsAut ι W := by
  haveI : IsAlgClosure K Ω := algClosure_up K Ω
  haveI : IsAlgClosure L Ω := algClosure_up L Ω
  haveI a : IsAbelianGalois K L := IsAbelianGalois.tower_top ℚ K L
  have e : (W.comp (resG ℚ K Ω)).comp (resG K L Ω) = W.comp (resG ℚ L Ω) := MonoidHom.ext fun _ => rfl
  rw [← e] at hirr haut
  have h1 := (_root_.UpperTheory.V.Z.Bc.solC_alt P cyc K L Ω (isSolvable_of_comm a.is_comm.comm) hC hL l ι 2 one_le_two (W.comp (resG ℚ K Ω))
    (hW.comp (continuous_restrictScalarsHom ℚ K Ω)) hirr (UpperTheory.solvable_polarized_restriction ℚ K Ω l ι 2 W hpol)).2 haut
  exact _root_.UpperTheory.V.Z.Bc.automorphic_rank_two_of_automorphic_restrict_of_finite_det P cyc2 hG (_root_.UpperTheory.V.Z.Bc.exists_residual_rep_quadratic_alt P) K Ω hK hC l ι W hW ((UpperTheory.galoisRep_irreducibility_criterion.1 _ _ _ 2 _).1 _ hirr) hfin h1
open UpperTheory.V UpperTheory.V.Af in
theorem UpperTheory.V.Z.Bc.isAutR_of_isAutC_comp_galEmb_of_odd_quadratic_char (P : _root_.UpperTheory.V.Af.HypothesesH') (cyc : Z.Bc.CycC) (cyc2 : Z.Bc.DescS) (hG : Z.Bc.GapTwo) :
  ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [IsAbelianGalois ℚ L] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    [Algebra L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (W : G ℚ Ω →* GL (Fin 2) (Qbar l)), Continuous W →
    IsCycWt l 0 (Matrix.GeneralLinearGroup.det.comp W) → IsIrr (W.comp (galEmb ℚ L Ω)) →
    (∃ (η : G ℚ Ω →* ℤˣ) (σ : G ℚ Ω), Sd.IsCC σ ∧ η σ = -1 ∧ ∀ s : G L Ω, η (galEmb ℚ L Ω s) = 1) →
    Sd.IsAutC ι (W.comp (galEmb ℚ L Ω)) → IsAutR ι W := by
  intro L Ω _ _ _ _ _ _ _ _ l _ ι W hW hdet hirr ⟨η, σ, hσ, hησ, hηL⟩ haut
  haveI : IsAlgClosure L Ω := algClosure_up L Ω
  obtain ⟨M, χ, hM, hχ, hθ⟩ := hdet
  rw [zpow_zero, one_mul] at hθ
  have hcont : Continuous (Matrix.GeneralLinearGroup.det.comp W) :=
    Matrix.GeneralLinearGroup.continuous_det.comp hW
  obtain ⟨k, hk, hpow⟩ := kills_pow hM hχ
  have halg : IsAlgChar ι (Matrix.GeneralLinearGroup.det.comp W) := by
    refine (_root_.UpperTheory.V.Af.algOfCyc_s P ℚ Ω l ι).1 _ hcont fun w _ => ?_
    obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
    exact ⟨A, hA, 0, k, hk, fun s _ => by rw [neg_zero, zpow_zero, mul_one, hθ, hpow]⟩
  obtain ⟨c, hc⟩ := cc_ex Ω
  obtain ⟨Q, hQ⟩ := pairing2 W c
  have hfin : ∃ N : ℕ, 0 < N ∧ ∀ s, Matrix.GeneralLinearGroup.det (W s) ^ N = 1 :=
    ⟨k, hk, fun s => by
      have e : Matrix.GeneralLinearGroup.det (W s) = χ s := DFunLike.congr_fun hθ s
      rw [e, hpow]⟩
  obtain ⟨K, hK, hC⟩ := Z.Bc.exists_quad L Ω η σ hσ hησ hηL
  have hpol : Sol.Pol ι W := ⟨ℚ, _, _, _, _, inferInstance, inferInstance, inferInstance, _, c, Q, halg,
    fun c c' h h' => by rw [hθ]; exact kills_cc hM hχ h h', hc, hQ⟩
  exact (_root_.UpperTheory.GalN.V.automorphy_bridge_of_printed_hida P ℚ Ω l ι 2 W).1.1 (via P cyc cyc2 hG K L Ω hK hC inferInstance l ι W hW hirr hpol hfin ((_root_.UpperTheory.GalN.V.automorphy_bridge_of_printed_hida P L Ω l ι 2 _).2.1.2 haut))
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSolDescent
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField UpperTheory.V.Af
theorem UpperTheory.V.Af.solvable_descent_of_printed_hida :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Af.SolDescent := by
  intro H F₀ F M Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hF hsol hplus hM l _ ι n hn r μ hr hirr hμ hs ⟨c, P, hc, hP⟩
  have hM' : IsCMField M := hM.resolve_left fun h => by
    obtain ⟨v⟩ : Nonempty (InfinitePlace M) := inferInstance
    exact (InfinitePlace.not_isReal_iff_isComplex.2 ((isTotallyComplex_of_algebra F M).isComplex v)) (h.isReal v)
  exact _root_.UpperTheory.V.Z.Bc.solC_alt H H.cyc F M Ω hsol hF hM' l ι n hn r hr hirr ⟨F₀, _, _, _, _, inferInstance, inferInstance, hplus.1, μ, c, P, hμ, hs, hc, hP⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TUpQuad
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.V.Af UpperTheory.V.Af.Bc in
theorem UpperTheory.V.Sd.up_quad_of_printed_results :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Sd.UpQuad := by
  intro hP F E Ω _ _ _ _ _ _ _ _ _ _ _ _ l _ ι hE n _ hn r hr ⟨π, hreg, hatt⟩ hirr
  obtain ⟨P, hBC⟩ := (_root_.UpperTheory.Gal.SV.quad_base_change_w_of_printed_results hP F E hE n hn π hreg).resolve_left
    fun ⟨η, hη, ht⟩ => _root_.UpperTheory.V.Af.Bc.noTwist_of_prints hP F E Ω l ι hE n r π hr hatt hirr η hη ht
  have h := UpperTheory.V.Br.bcAtt0 F E Ω l ι n r π P hBC.toIsBC0
  exact ⟨P, h.1 hreg, h.2 hatt ((Bc.irrBasic.1 _ Unit _ n _).2.1 hirr)⟩
end
end

