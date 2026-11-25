module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepresentationValueAtOriginLeviFactor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharEqOneOfTrivialSplitPlacesCMStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralCompAut
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelWeilSectionLawDiagonalLagrangian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicRapidDecayOfMemAdelicSchwartzSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicStoneVonNeumannLagrangianUniqueness
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmittedEqDiagonalLagrangianThetaIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagLagrangian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaReNonneg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HTensDiagEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralNeZeroOfCocompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixMemSpanIncM
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormAdelicThetaSumSchroedingerRationalPairInvari
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ContinuousTransportFApplyK
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.InvHerm
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Mfac
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramHspOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.MeanSquareAddFundamentalDomainOfCocompact
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.CAFInvol
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.DiagonalLagrangianIntegralSiegelParabolicTransfo
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LeviGLInvVal
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Periodic
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SplitPlaceSiegelLawDiagonalLagrangianCharacter
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.OneAddPow
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalMatricesDiscreteCocompactAdelicMatrixSpa
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LagrIntRhoInvK, Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SplittingCharacterRestrictedEta

-- ===== clump member: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LagrIntRhoInvK =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LagrIntRhoInvK", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicRapidDecayOfMemAdelicSchwartzSpace\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicStoneVonNeumannLagrangianUniqueness\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmittedEqDiagonalLagrangianThetaIntegral\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagLagrangian\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaReNonneg\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HTensDiagEqZero\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralNeZeroOfCocompact\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixMemSpanIncM\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormAdelicThetaSumSchroedingerRationalPairInvari\npublic import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ContinuousTransportFApplyK\npublic import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.InvHerm\npublic import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Mfac\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramHspOf\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz\npublic import Development.AbelianVarietyTheory.Proofs.HeightProofs.MeanSquareAddFundamentalDomainOfCocompact\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF\n\n"}
section -- clump:auto
/-! # LagrIntRhoInvK: Consolidated global theta-kernel definitions and proofs (LagrIntRhoInvK). -/
@[expose] public section

open GlobalTheory.WeilSchrodinger (thetaTr)
open GlobalTheory.WeilSchrodinger.DblTargetF (dblG)
open UpperTheory.TP.W (GoodK)
open scoped TensorProduct Matrix
open scoped Matrix TensorProduct
open GlobalTheory.WeilM (schA)

section
open scoped Classical TensorProduct Matrix
open GlobalTheory.ThetaTrCont NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  MeasureTheory GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  Formalism.IndefR.DatumF
noncomputable section
namespace GlobalTheory.LagrThetaAdm
open GlobalTheory.WeilSchrodinger
theorem exists_admissible_eq_lagrangian_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    GoodK σ B → ∀ (nS nT : ℕ) (JT : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS)
      E) (ξ : AF F ⊗[F] E)
      (κ : Type) [Fintype κ]
      (co : Darboux (symp (cA σ) ξ (incM F (dblG JT)ᵀ) (incM F JB)) κ),
      (∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : κ → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∃ l₂ ∈ (adeleClass F).adm κ, ∀ Φ ∈ schA F κ, l₂ Φ = GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) :
        Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id)
        (thetaTr F co B.ψ Φ) := by
  intro F E _ _ _ _ _ σ B hB nS nT JT JB ξ κ _ co hrat ν 𝓕 hν h𝓕
  have hψ := GlobalTheory.StdCharFromIsStd.isCharAF hB.std
  set Cm :=
    (diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id with hCm
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  have : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  have : Countable (ratLF F E nS nT) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hfin :=
    GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WOF F E nS nT) (ratLF F E nS nT) hK hKc ν h𝓕
  have : IsFiniteMeasure (ν.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  have : IsModuleTopology (AF F) (Matrix (Fin (nT + nT)) (Fin nS) (AE F E)) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin (nT + nT) → Fin nS → AE F E))
  have hce : Continuous co.e := IsModuleTopology.continuous_of_linearMap co.e.toLinearMap
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hCu : Continuous fun u : WOF F E nS nT => Cm * u := continuous_const.matrix_mul continuous_id
  have hcont : ∀ Φ ∈ schA F κ, Continuous fun u : WOF F E nS nT => thetaTr F co B.ψ Φ (Cm * u) :=
    fun Φ hΦ => ((schA_cont F B.ψ hψ.1 hψ.2.1 hΦ).2.comp hce).comp hCu
  have hint : ∀ Φ ∈ schA F κ, Integrable (fun u => thetaTr F co B.ψ Φ (Cm * u)) (ν.restrict 𝓕) := fun Φ hΦ => by
    obtain ⟨C, hC⟩ := thetaSum_schA_bdd F B.ψ hψ.1 hψ.2.1 hΦ
    exact Integrable.of_bound (hcont Φ hΦ).aestronglyMeasurable C (Filter.Eventually.of_forall fun u => hC _)
  have hadd : ∀ Φ ∈ schA F κ, ∀ Ψ ∈ schA F κ, ∀ w,
      thetaTr F co B.ψ (Φ + Ψ) w = thetaTr F co B.ψ Φ w + thetaTr F co B.ψ Ψ w := by
    intro Φ hΦ Ψ hΨ w
    have e : schr B.ψ (co.e w) (Φ + Ψ) = schr B.ψ (co.e w) Φ + schr B.ψ (co.e w) Ψ :=
      funext fun x => by simp [schr, mul_add]
    show thetaSum F (schr B.ψ (co.e w) (Φ + Ψ)) = thetaSum F (schr B.ψ (co.e w) Φ) + thetaSum F (schr B.ψ (co.e w) Ψ)
    rw [e]
    exact ((schA_cont F B.ψ hψ.1 hψ.2.1 hΦ).1 _).tsum_add ((schA_cont F B.ψ hψ.1 hψ.2.1 hΨ).1 _)
  have hsmul : ∀ (a : ℂ) (Φ : (κ → AF F) → ℂ) w, thetaTr F co B.ψ (a • Φ) w = a * thetaTr F co B.ψ Φ w := by
    intro a Φ w
    have e : schr B.ψ (co.e w) (a • Φ) = a • schr B.ψ (co.e w) Φ := funext fun x => by
      simp only [schr, Pi.smul_apply, smul_eq_mul]
      ring
    show thetaSum F (schr B.ψ (co.e w) (a • Φ)) = a * thetaSum F (schr B.ψ (co.e w) Φ)
    rw [e, thetaSum_smul]
  let L : schA F κ →ₗ[ℂ] ℂ :=
    { toFun := fun Φ => GlobalTheory.LagrTheta.lagrInt ν 𝓕 Cm (thetaTr F co B.ψ Φ)
      map_add' := fun Φ Ψ => by
        show ∫ u in 𝓕, thetaTr F co B.ψ (Φ.1 + Ψ.1) (Cm * u) ∂ν =
          ∫ u in 𝓕, thetaTr F co B.ψ Φ.1 (Cm * u) ∂ν + ∫ u in 𝓕, thetaTr F co B.ψ Ψ.1 (Cm * u) ∂ν
        simp_rw [hadd Φ.1 Φ.2 Ψ.1 Ψ.2]
        exact integral_add (hint _ Φ.2) (hint _ Ψ.2)
      map_smul' := fun a Φ => by
        show ∫ u in 𝓕, thetaTr F co B.ψ (a • Φ.1) (Cm * u) ∂ν = a • ∫ u in 𝓕, thetaTr F co B.ψ Φ.1 (Cm * u) ∂ν
        simp_rw [hsmul]
        rw [integral_const_mul, smul_eq_mul] }
  obtain ⟨l, hl⟩ := LinearMap.exists_extend L
  have hlL : ∀ Φ (hΦ : Φ ∈ schA F κ), l Φ = L ⟨Φ, hΦ⟩ := fun Φ hΦ => LinearMap.congr_fun hl ⟨Φ, hΦ⟩
  refine ⟨l, ?_, fun Φ hΦ => hlL Φ hΦ⟩
  intro g hg
  obtain ⟨k, c, hc, hb⟩ := thetaSum_pure_le F B.ψ hψ.2.1 hg
  have hmem : ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, pureA F f g ∈ schA F κ := fun f =>
    Submodule.subset_span ⟨f, g, hg, rfl⟩
  have hsn : ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f =
        ((Finset.Iic (k, 0)).sup (schwartzSeminormFamily ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)) f := by
    intro f
    rw [Seminorm.finset_sup_apply, Seminorm.finset_sup_apply]
    congr 2
    funext i
    simp [schwartzSeminormFamily, SchwartzMap.seminorm_apply]
  refine ⟨SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ) (fun f => L ⟨pureA F f g, hmem f⟩)
    (fun f f' => ?_) (fun a f => ?_) ⟨Finset.Iic (k, 0), c * ν.real 𝓕, mul_nonneg hc measureReal_nonneg, fun f => ?_⟩,
    fun f => ?_⟩
  · rw [← map_add (f := _)]
    congr 1
    exact Subtype.ext (funext fun x => by simp [pureA, add_mul])
  · rw [RingHom.id_apply, ← map_smul]
    congr 1
    exact Subtype.ext (funext fun x => by simp [pureA, mul_assoc])
  · show ‖∫ u in 𝓕, thetaTr F co B.ψ (pureA F f g) (Cm * u) ∂ν‖ ≤ _
    refine (norm_setIntegral_le_of_norm_le_const hfin fun u _ => hb f (co.e (Cm * u))).trans (le_of_eq ?_)
    rw [hsn]
    ring
  · exact hlL _ (hmem f)
end GlobalTheory.LagrThetaAdm
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
  GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  Formalism.IndefR.DatumF
open GlobalTheory.LagrTheta (lagrInt)
noncomputable section
open scoped Pointwise in
open GlobalTheory.LagrThetaInv in
theorem GlobalTheory.LagrThetaInv.lagrInt_rho_inv_k : ∀ (F E :
  Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    GoodK σ B → ∀ (nS nT : ℕ) (JT : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS)
      E) (ξ : AF F ⊗[F] E)
      (κ : Type) [Fintype κ]
      (co : Darboux (symp (cA σ) ξ (incM F (dblG JT)ᵀ) (incM F JB)) κ),
      (∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : κ → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ (u : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)), ∀ φ ∈ schA F κ,
        lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F]
          E)).submatrix finSumFinEquiv.symm id) (thetaTr F co B.ψ (co.rho B.ψ (((diagCols
          (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * u) φ)) =
          lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F]
          E)).submatrix finSumFinEquiv.symm id) (thetaTr F co B.ψ φ) := by
  intro F E _ _ _ _ _ σ B hB nS nT JT JB ξ κ _ co hco ν 𝓕 _ h𝓕 u φ hφ
  change lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT)
      (thetaTr F co B.ψ (co.rho B.ψ (dC (AF F ⊗[F] E) nT * u) φ)) =
    lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT) (thetaTr F co B.ψ φ)
  set g : WOF F E nS nT → ℂ := fun v => thetaTr F co B.ψ φ (dC (AF F ⊗[F] E) nT * v)
    with hg
  have h1 : ∀ v : WOF F E nS nT, thetaTr F co B.ψ (co.rho B.ψ (dC (AF F ⊗[F] E) nT * u) φ)
      (dC (AF F ⊗[F] E) nT * v) = g (v + u) := by
    intro v
    simp only [hg, thetaTr, Darboux.rho]
    rw [schr_dC]
  have h2 : ∀ (r : ratLF F E nS nT) (v : WOF F E nS nT), g (r +ᵥ v) = g v := by
    rintro ⟨r, γ, rfl⟩ v
    obtain ⟨y, z, hyz⟩ := hco (dC E nT * γ)
    have hr : ((incAF F E).toAddMonoidHom.mapMatrix γ : WOF F E nS nT) = γ.map (incAF F E) := rfl
    show thetaTr F co B.ψ φ (dC (AF F ⊗[F] E) nT * (_ + v)) = _
    simp only [hg, thetaTr, Darboux.rho]
    rw [← schr_dC, hr, dC_mul_rat, hyz, GlobalTheory.ThetaQuasiRat.thetaSum_schr_rat F B.ψ hB.std.2.1 y z]
  have : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  have : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) _
  have : ContinuousAdd (WOF F E nS nT) := inferInstanceAs (ContinuousAdd (Fin nT → Fin nS → AF F ⊗[F] E))
  have : MeasurableAdd (WOF F E nS nT) :=
    ⟨fun c => (continuous_const_add c).measurable, fun c => (continuous_add_const c).measurable⟩
  have : MeasurableConstVAdd (ratLF F E nS nT) (WOF F E nS nT) :=
    ⟨fun r => (continuous_const_add (r : WOF F E nS nT)).measurable⟩
  have : VAddInvariantMeasure (ratLF F E nS nT) (WOF F E nS nT) ν :=
    ⟨fun r s _ => measure_preimage_add ν (r : WOF F E nS nT) s⟩
  have : VAddCommClass (WOF F E nS nT) (ratLF F E nS nT) (WOF F E nS nT) :=
    ⟨fun a r x => add_left_comm a (r : WOF F E nS nT) x⟩
  have : Countable (ratLF F E nS nT) := by
    have : Countable E := by
      have : FiniteDimensional ℚ E := inferInstance
      exact ((Module.finBasis ℚ E).equivFun).injective.countable
    have : Countable (Matrix (Fin nT) (Fin nS) E) := inferInstanceAs (Countable (Fin nT → Fin nS → E))
    exact (Set.countable_range ((incAF F E).toAddMonoidHom.mapMatrix (m := Fin nT) (n := Fin nS))).to_subtype
  unfold lagrInt
  simp_rw [h1]
  rw [← (measurePreserving_add_right ν u).setIntegral_image_emb (measurableEmbedding_addRight u) g 𝓕]
  have hF' : IsAddFundamentalDomain (ratLF F E nS nT) ((· + u) '' 𝓕) ν := by
    have hs : (· + u) '' 𝓕 = ((u : WOF F E nS nT) +ᵥ 𝓕 : Set (WOF F E nS nT)) := by
      rw [← Set.image_vadd]
      congr 1; funext v
      exact add_comm v u
    rw [hs]
    exact h𝓕.vadd_of_comm (G' := WOF F E nS nT) (u : WOF F E nS nT)
  exact hF'.setIntegral_eq h𝓕 h2
end
end

section
namespace GlobalTheory.LagrUniq
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
  GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  Formalism.IndefR.DatumF
theorem exists_lagrInt_ne_zero_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ :
  E →ₐ[F] E) (B : Base F E),
    GoodK σ B → ∀ (nS nT : ℕ) (JT : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS)
      E) (ξ : AF F ⊗[F] E)
      (κ : Type) [Fintype κ]
      (co : Darboux (symp (cA σ) ξ (incM F (dblG JT)ᵀ) (incM F JB)) κ),
      (∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : κ → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∃ φ ∈ schA F κ, GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F
        ⊗[F] E)).submatrix finSumFinEquiv.symm id) (thetaTr F co B.ψ φ) ≠ 0 := by
  intro F E _ _ _ _ _ σ B hB nS nT JT JB ξ κ _ co hco ν 𝓕 hν h𝓕
  have hstd := hB.std
  have : IsModuleTopology (AF F) (WOF F E nS nT) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin nT → Fin nS → AF F ⊗[F] E))
  set C :=
    (diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id with hC
  set C₀ :=
    (diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) E).submatrix finSumFinEquiv.symm id with hC₀
  have hCC : C = incM F C₀ := by
    ext i j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    rcases i with i | i <;> by_cases h : i = j <;>
      simp only [hC, hC₀, incM, diagCols, Matrix.submatrix_apply, Matrix.map_apply, Equiv.symm_apply_apply, id,
        Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.one_apply, h, ite_true, ite_false, map_one,
          map_zero]
  let mC : WOF F E nS nT →ₗ[AF F] Matrix (Fin (nT + nT)) (Fin nS) (AF F ⊗[F] E) :=
    { toFun := fun u => C * u
      map_add' := fun u v => Matrix.mul_add _ _ _
      map_smul' := fun t u => Matrix.mul_smul _ _ _ }
  let Lm := co.e.toLinearMap ∘ₗ mC
  have hLm : ∀ u, Lm u = co.e (C * u) := fun u => rfl
  let S := LinearMap.range Lm
  have hiso : ∀ s ∈ S, ∀ s' ∈ S, s.1 ⬝ᵥ s'.2 = s'.1 ⬝ᵥ s.2 := by
    rintro _ ⟨u, rfl⟩ _ ⟨u', rfl⟩
    have h := co.form (C * u) (C * u')
    rw [GlobalTheory.WeilDiagIso.symp_diag_eq_zero F E σ nS nT JT JB ξ u u'] at h
    rw [hLm, hLm]
    exact (sub_eq_zero.mp h.symm)
  have hrat : ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
      Lm (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := by
    intro x
    have e : C * incM F x = incM F (C₀ * x) := by
      rw [hCC]
      simp only [incM]
      exact (Matrix.map_mul (f := (inclR (AF F) : E →+* AF F ⊗[F] E))).symm
    obtain ⟨y, z, h⟩ := hco (C₀ * x)
    exact ⟨y, z, by rw [hLm, e, h]⟩
  have hspan : S ≤ Submodule.span (AF F) {s | s ∈ S ∧ ∃ y z : κ → F,
      s = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))} := by
    rintro _ ⟨u, rfl⟩
    have hu := Submodule.mem_map_of_mem (f := Lm) (GlobalTheory.matrix_mem_span_incM F E nT nS u)
    rw [Submodule.map_span] at hu
    refine Submodule.span_mono ?_ hu
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    obtain ⟨y, z, h⟩ := hrat x
    exact ⟨⟨incM F x, rfl⟩, y, z, h⟩
  obtain ⟨Φ, hΦ, hcont, hre, hre0⟩ := GlobalTheory.ThetaPosIso.exists_theta_re_nonneg F B.ψ hstd κ S hiso hspan
  refine ⟨Φ, hΦ, ?_⟩
  have hI : ∀ u : WOF F E nS nT, thetaTr F co B.ψ Φ (C * u) = thetaSum F (schr B.ψ (Lm u)
    Φ) :=
    fun u => rfl
  show ∫ u in 𝓕, thetaTr F co B.ψ Φ (C * u) ∂ν ≠ 0
  simp_rw [hI]
  refine GlobalTheory.PeriodicPositiveIntegral.integral_ne_zero F E nS nT (fun u =>
    thetaSum F (schr B.ψ (Lm u) Φ)) ?_ ?_ ?_ ?_ ν 𝓕 hν h𝓕
  · exact hcont.comp (IsModuleTopology.continuous_of_linearMap Lm)
  · rintro _ ⟨γ₀, rfl⟩ u
    obtain ⟨y, z, h⟩ := hrat γ₀
    have e1 : Lm (((incAF F E).toAddMonoidHom.mapMatrix (m := Fin nT) (n := Fin nS)) γ₀ + u) = Lm (incM F γ₀) + Lm u :=
      by
      rw [map_add (f := _)]; rfl
    have hr : Lm (incM F γ₀) ∈ S := ⟨incM F γ₀, rfl⟩
    have hw : Lm u ∈ S := ⟨u, rfl⟩
    have hi := hiso _ hw _ hr
    rw [h] at hi
    show thetaSum F (schr B.ψ (Lm (_ + u)) Φ) = _
    rw [e1, h, GlobalTheory.ThetaRatInv.thetaSum_schr_rat_add B.ψ hstd.2.1 Φ y z (Lm u), hi, sub_self, mul_zero,
      AddChar.map_zero_eq_one, one_mul]
  · intro u; exact hre _ ⟨u, rfl⟩
  · show 0 < (thetaSum F (schr B.ψ (Lm 0) Φ)).re
    rw [map_zero]; exact hre0
theorem lagr_invariant_unique_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ :
  E →ₐ[F] E) (B : Base F E),
    GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT)
      E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : Darboux (symp (cA σ) ξ (incM F (dblG JT)ᵀ) (incM F JB)) κ),
        (∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : κ → F,
          co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ l ∈ (adeleClass F).adm κ,
        (∀ z : Matrix (Fin nS) (Fin nT) (AF F ⊗[F] E), ∀ φ ∈ schA F κ,
          l ((GlobalTheory.WeilSchrodinger.transD (cA σ) co).rho B.ψ (z * ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT)
            (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id)ᵀ) φ) = l φ) →
        ∃ c : ℂ, ∀ Φ ∈ schA F κ, l Φ = c * GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin
          nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (thetaTr F co B.ψ
          Φ) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσξ₀ JB ξ hξ κ _ co hco ν 𝓕 hν h𝓕 l hl hinv
  have hstd := hB.std
  obtain ⟨L, hiso, hdim, hL⟩ := GlobalTheory.WeilSchrodinger.DiagLagr.exists_diag_lagrangian F E σ nS nT JT JB ξ κ co
    hco
  obtain ⟨l₂, hl₂, he⟩ := GlobalTheory.LagrThetaAdm.exists_admissible_eq_lagrangian_integral F E σ B hB nS nT JT
    JB ξ κ co hco ν 𝓕 hν h𝓕
  obtain ⟨φ₀, hφ₀, hne⟩ := exists_lagrInt_ne_zero_k F E σ B hB nS nT JT JB ξ κ co hco ν 𝓕
    hν h𝓕
  have hrho : ∀ (u : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)) (φ : (κ → AF F) → ℂ),
      (GlobalTheory.WeilSchrodinger.transD (cA σ) co).rho B.ψ (uᵀ * ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin
        nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id)ᵀ) φ = co.rho B.ψ (((diagCols (Fin nT) : Matrix (Fin nT ⊕
        Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * u) φ := by
    intro u φ
    rw [GlobalTheory.WeilSchrodinger.transD_rho, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_transpose]
  have hmem : ∀ w, ∀ φ ∈ schA F κ, co.rho B.ψ w φ ∈ schA F κ := fun w φ hφ =>
    GlobalTheory.HeisSchA.schr_mem_schA B.ψ hstd _ φ hφ
  have key : ∀ l' : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ,
      (∀ (u : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)), ∀ φ ∈ schA F κ, l' (co.rho B.ψ (((diagCols (Fin nT) : Matrix (Fin
        nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * u) φ) = l' φ) →
      ∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F κ,
        l' (schr B.ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l' φ :=
          by
    intro l' h t w hw φ hφ
    obtain ⟨u, hu⟩ := hL t w hw
    rw [← hu]
    exact h u φ hφ
  obtain ⟨c, hc⟩ := GlobalTheory.AdelicSvN.main F B.ψ hstd κ L hiso hdim l hl l₂ hl₂
    (key l (fun u φ hφ => by rw [← hrho]; exact hinv _ φ hφ))
    (key l₂ (fun u φ hφ => by
      rw [he _ (hmem _ φ hφ), he φ hφ]
      exact GlobalTheory.LagrThetaInv.lagrInt_rho_inv_k F E σ B hB nS nT JT JB ξ κ co hco ν 𝓕 hν h𝓕 u φ hφ))
    ⟨φ₀, hφ₀, by rw [he φ₀ hφ₀]; exact hne⟩
  exact ⟨c, fun Φ hΦ => by rw [hc Φ hΦ, he Φ hΦ]⟩
end GlobalTheory.LagrUniq
end

section
abbrev _root_.GlobalTheory.T.lagrangian_integral_theta_model :=
  GlobalTheory.LagrThetaAdm.exists_admissible_eq_lagrangian_integral
end

noncomputable section
namespace GlobalTheory.TransportF
open Formalism.IndefR.DatumF Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.LFun GlobalTheory.WeilM IsDedekindDomain
  NumberField GlobalTheory.ThetaTransform GlobalTheory.SWQ
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E} {JA
  : Matrix (Fin nT) (Fin nT) E} {JB : Matrix (Fin nS) (Fin nS) E} {ξ : AF F ⊗[F] E}
variable {κ : Type} [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ)
theorem exists_isTransportF_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E
  →ₐ[F] E) (B : Base F E),
    GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT)
      E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), IsHeckeCharF χS →
        IsHeckeCharF χT →
        ResEtaF χS nS → ResEtaF χT nT →
        ∀ ω : GAF σ JS × GAF σ JT →* Module.End ℂ
          (WOF F E nS nT → ℂ),
        IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∃ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ0 hσξ χS χT _ _ _ _ ω hω JA JB ξ hA hB' κ _ co hrat
  have hR := hB.cm.1
  have hψ := hω.std.1
  let τ := Fintype.equivFin κ
  have he : ∀ w w', symplOF σ JS JT ξ₀ w w' = symV (numCoordF co τ w) (numCoordF co τ w') := fun w w' => by
    rw [symplOF_eq_symp hA hB', co.form]
    simp only [symV, numCoordF_apply, comp_equiv_dotProduct_comp_equiv]
  have hr : ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin (Fintype.card κ) → F,
      numCoordF co τ (ratWF x) = (rat y, rat z) := fun x => by
    obtain ⟨y, z, h⟩ := hrat x
    exact ⟨y ∘ τ.symm, z ∘ τ.symm, by rw [numCoordF_apply]; erw [h]; rfl⟩
  have hadd : ∀ Φ ∈ schA F κ, ∀ Φ' ∈ schA F κ,
      thetaTr F co B.ψ (Φ + Φ') =
        thetaTr F co B.ψ Φ + thetaTr F co B.ψ Φ' :=
          fun Φ hΦ Φ' hΦ' => by
    simp only [thetaTr_eqF co τ]
    exact congrArg (· ∘ numCoordF co τ) (thV_add hR hψ
      (GlobalTheory.SchwartzDecay.decay_of_mem_schA _ _ _ (comp_mem_schA τ hΦ))
      (GlobalTheory.SchwartzDecay.decay_of_mem_schA _ _ _ (comp_mem_schA τ hΦ')))
  have hinj : ∀ Φ ∈ schA F κ, ∀ Φ' ∈ schA F κ,
      thetaTr F co B.ψ Φ = thetaTr F co B.ψ Φ' → Φ = Φ' :=
    fun Φ hΦ Φ' hΦ' h => by
    simp only [thetaTr_eqF co τ] at h
    have h2 := thV_injOn hR hψ (comp_mem_schA τ hΦ) (comp_mem_schA τ hΦ')
      ((numCoordF co τ).surjective.injective_comp_right h)
    funext x
    simpa [Function.comp_def] using congrFun h2 (x ∘ τ.symm)
  have hon : ∀ f : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ B.ψ f ↔
      ∃ Φ ∈ schA F κ, thetaTr F co B.ψ Φ = f := fun f => by
    constructor
    · intro hf
      obtain ⟨Φ, hΦ, h⟩ := GlobalTheory.T.schrodinger_model_intertwining F E σ B hB nS nT JS JT hS hT ξ₀ hξ0 hσξ
        hω.std _ (numCoordF co τ) he hr f hf
      refine ⟨_, comp_mem_schA τ.symm hΦ, ?_⟩
      rw [thetaTr_eqF co τ, ← h]
      congr 2
      funext x
      simp [Function.comp_def]
    · rintro ⟨Φ, hΦ, rfl⟩
      rw [thetaTr_eqF co τ]
      exact GlobalTheory.T.schrodinger_model_isomorphism F E σ B hB nS nT JS JT hS hT ξ₀ hξ0 hσξ hω.std _
        (numCoordF co τ) he hr _
        (comp_mem_schA τ hΦ)
  obtain ⟨om, hom⟩ := exists_transport' _ _ _ hadd (thetaTr_smulF co) hinj hon
    (ω.comp (pairHomF hS hξ0 hA hB')) fun p f hf => hω.om_pres _ f hf
  refine ⟨om, ?_⟩
  intro a b g h hh hg Φ hΦ
  have e :=
    congrArg ω (pairHomF_eq hS hξ0 hA hB' a b g h hh hg)
  have h2 := hom (a, b) Φ hΦ
  exact ⟨h2.1, h2.2.trans (LinearMap.congr_fun e _)⟩
end GlobalTheory.TransportF
end

section
open Formalism.IndefR.DatumF Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.LFun GlobalTheory.WeilM IsDedekindDomain
  NumberField MeasureTheory
noncomputable section
namespace PositivityTheory.ThKW.PhaseFourierInjectivity
open PositivityTheory.ThKW.ModulusFactorDefinition
section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem exists_coord_k {B : Base F E} (hB : GoodK σ B) {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin
  nS) E}
    {JT : Matrix (Fin nT) (Fin nT) E} (hS : IsHermND σ JS) (hT : IsHermND σ JT) {ξ₀ : E} (hξ : ξ₀ ≠ 0) (hσ : σ ξ₀ = -ξ₀)
      :
    (-1 : AF F ⊗[F] E) • incM F (-(ξ₀ • JS⁻¹)) = incM F (ξ₀ • JS⁻¹) ∧
    ∃ co : Darboux (symp (cA σ) (-1) (incM F JTᵀ) (incM F (-(ξ₀ • JS⁻¹)))) (Fin nT × Fin nS),
      (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin nT × Fin nS → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) ∧
      ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → ∃ Φ ∈ schA F (Fin nT × Fin nS), thetaTr F co B.ψ
        Φ = f := by
  have eB : (-1 : AF F ⊗[F] E) • incM F (-(ξ₀ • JS⁻¹)) = incM F (ξ₀ • JS⁻¹) := by
    funext i j
    simp [incM]
  obtain ⟨co, hrat⟩ : ∃ co : Darboux (symp (cA σ) (-1) (incM F JTᵀ) (incM F (-(ξ₀ • JS⁻¹)))) (Fin nT × Fin nS),
      ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin nT × Fin nS → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) :=
    GlobalTheory.RatDarboux.exists_darboux (AF F) hB.cm.2.2.1 σ (GlobalTheory.SplitDetCharF.sig_invol hB.cm)
    (JA := JTᵀ) (JB := -(ξ₀ • JS⁻¹)) (fun i j => hT.1 j i)
    (fun i j => by
      simp only [Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul, map_neg, map_mul, hσ, inv_herm hS]; ring)
    (by rw [Matrix.det_transpose]; exact hT.2)
    (by
      rw [← neg_smul, Matrix.det_smul]
      exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 hξ)) (Matrix.isUnit_nonsing_inv_det _ (Ne.isUnit hS.2)).ne_zero)
  refine ⟨eB, co, hrat, fun f hf => ?_⟩
  let τ := Fintype.equivFin (Fin nT × Fin nS)
  have he : ∀ w w', symplOF σ JS JT ξ₀ w w' =
      GlobalTheory.ThetaTransform.symV (GlobalTheory.TransportF.numCoordF (σ :=
        σ) co τ w) (GlobalTheory.TransportF.numCoordF co τ w') := fun w w' => by
    rw [GlobalTheory.TransportF.symplOF_eq_symp rfl eB]
    refine (co.form w w').trans ?_
    simp only [GlobalTheory.ThetaTransform.symV, GlobalTheory.TransportF.numCoordF_apply,
      comp_equiv_dotProduct_comp_equiv]
  have hr : ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin (Fintype.card (Fin nT × Fin nS)) → F,
      GlobalTheory.TransportF.numCoordF co τ (ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z) :=
        fun x => by
    obtain ⟨y, z, h⟩ := hrat x
    exact ⟨y ∘ τ.symm, z ∘ τ.symm, by rw [GlobalTheory.TransportF.numCoordF_apply]; erw [h]; rfl⟩
  obtain ⟨Φ, hΦ, h⟩ := GlobalTheory.T.schrodinger_model_intertwining F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσ
    (GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood_k F E σ B hB) _ (GlobalTheory.TransportF.numCoordF (σ :=
      σ) co τ) he hr f hf
  refine ⟨_, GlobalTheory.TransportF.comp_mem_schA τ.symm hΦ, ?_⟩
  rw [GlobalTheory.TransportF.thetaTr_eqF co τ, ← h]
  congr 2
  funext x
  congr 1; funext i
  simp
end
theorem cont_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B :
  Base F E),
    GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT)
      E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle) (ωd : GAF σ JS × GAF σ (dblG JT) →*
            Module.End ℂ (WOF F E nS (nT + nT) → ℂ)),
        IsWeilDatumOF σ JS (dblG JT)
            (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ f, IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ f →
        Continuous fun h : GAF σ (dblG JT) =>
          GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT) (ωd (1, h) f) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσ ν 𝓕 hν h𝓕 χS ωd hω f hf
  have hT' := GlobalTheory.WeilSchrodinger.DblTargetF.isHermND_dblG hT
  obtain ⟨eB, co, hrat, hon⟩ := exists_coord_k hB hS hT' hξ hσ
  obtain ⟨Φ, hΦ, rfl⟩ := hon f hf
  obtain ⟨om, hom⟩ := GlobalTheory.TransportF.exists_isTransportF_k F E σ B hB _ _ JS _ hS hT' ξ₀ hξ hσ χS 1
    hω.hecS hω.hecT hω.resS
    hω.resT ωd hω _ _ _ rfl eB _ co hrat
  have hc := GlobalTheory.WeilContF.continuous_transportF_k F E σ B hB _ _ JS _ hS hT' ξ₀ hξ hσ χS 1 hω.hecS
    hω.hecT hω.resS
    hω.resT ωd hω _ _ _ rfl eB _ co hrat om hom
  obtain ⟨l, hl, hl'⟩ := GlobalTheory.T.lagrangian_integral_theta_model F E σ B hB nS nT JT _ _ _ co hrat ν 𝓕 hν
    h𝓕
  let a : GAF σ (dblG JT) →
      UG (cA σ) (incM F (dblG JT)ᵀ) := fun h => ⟨matHomF σ _ h, mem_UG h⟩
  have ha : Continuous a := Continuous.subtype_mk continuous_subtypeVal _
  refine ((hc l hl Φ hΦ).comp (ha.prodMk (continuous_const (y := 1)))).congr fun h => ?_
  obtain ⟨h1, h2⟩ := hom (a h) 1 1 h rfl (by
    rw [inv_one]
    exact Matrix.transpose_one.symm) Φ hΦ
  show l (om (a h, 1) Φ) = _
  exact (hl' _ h1).trans (congrArg (GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT)) h2)
end PositivityTheory.ThKW.PhaseFourierInjectivity
end
end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LagrIntRhoInvK =====

-- ===== clump member: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SplittingCharacterRestrictedEta =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SplittingCharacterRestrictedEta", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepresentationValueAtOriginLeviFactor\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharEqOneOfTrivialSplitPlacesCMStatement\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralCompAut\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelWeilSectionLawDiagonalLagrangian\npublic import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LagrIntRhoInvK\npublic import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.CAFInvol\npublic import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.DiagonalLagrangianIntegralSiegelParabolicTransfo\npublic import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LeviGLInvVal\npublic import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Periodic\npublic import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SplitPlaceSiegelLawDiagonalLagrangianCharacter\npublic import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.OneAddPow\npublic import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff\npublic import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalMatricesDiscreteCocompactAdelicMatrixSpa\npublic import Formalism.LocalToGlobal.IndefiniteReal.DatumF\n\n"}
section -- clump:auto
/-! # SplittingCharacterRestrictedEta: Consolidated global theta-kernel definitions and proofs (SplittingCharacterRestrictedEta). -/
@[expose] public section

open GlobalTheory.WeilSchrodinger.DblTargetF (dblG)
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.SplitLagrF
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
  GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  Formalism.IndefR.DatumF
theorem exists_levi_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
  (B : Base F E),
    UpperTheory.TP.W.GoodK σ B → ∀ (nT : ℕ) (JT : Matrix (Fin nT) (Fin nT) E), IsHermND σ JT →
      ∀ e, IsSplitIdemF σ e → ∀ t : GL (Fin nT) (AF F ⊗[F] E),
        (∀ i j, (e + cAF σ e) * (t.1 - 1) i j = (t.1 - 1) i j) →
      ∃ h : GAF σ (dblG JT),
        mtF σ (dblG JT) h * dC F E nT = dC F E nT * t.1 ∧
        SuppAtF σ e (dblG JT) h ∧
        (∃ M : Matrix (Fin nT) (Fin nT) (AF F ⊗[F] E), IsUnit M.det ∧ ∀ (nS : ℕ) (y : WOF F E nS nT),
          mtF σ (dblG JT) h⁻¹ * (aC F E nT * y) = aC F E nT * (M * y)) ∧
        ∃ x : (AF F ⊗[F] E)ˣ, IsDetAtF σ e (dblG JT) h x ∧
          ∀ (χ : (AF F ⊗[F] E)ˣ →* Circle) (m : ℕ), ResEtaF χ m → χ x = χ (Matrix.GeneralLinearGroup.det t) := by
  intro F E _ _ _ _ _ σ B hB n JT hT e he t ht
  have hc : IsCMExt F E σ := hB.cm
  have hcc := cAF_invol hc
  obtain ⟨r, hr⟩ : ∃ r : AEF F E, 2 * r = 1 := by
    have h := (IsUnit.mk0 (2 : F) two_ne_zero).map (algebraMap F (AF F ⊗[F] E))
    rw [map_ofNat] at h
    exact h.exists_right_inv
  have hJ : ((JR (F := F) (AF F) JT).map (cAF σ))ᵀ = JR (F := F) (AF F) JT := by
    ext i j
    show (1 : AF F) ⊗ₜ[F] σ (JT j i) = (1 : AF F) ⊗ₜ[F] JT i j
    rw [hT.1]
  have hu : IsUnit (JR (F := F) (AF F) JT).det := by
    have := ((Ne.isUnit hT.2).map (inclR (F := F) (AF F)))
    rwa [RingHom.map_det] at this
  have ha : cAF σ (e + cAF σ e) = e + cAF σ e := by rw [RingHom.map_add (f := _), hcc, add_comm]
  obtain ⟨H, H', g1, g2, g3, g4, g5, ⟨M, hM, g6⟩, g7⟩ := levi_alg (cAF σ) hcc r hr _ hJ hu _ ha t.1 (t⁻¹).1
    t.mul_inv t.inv_mul (by ext i j; exact ht i j)
  have eJ : JR (F := F) (AF F) (dblG JT) =
      (Matrix.fromBlocks (JR (F := F) (AF F) JT) 0 0 (-JR (F := F) (AF F) JT)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm := by
    ext i j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [dblG, JR, Matrix.reindex_apply, Matrix.submatrix_apply,
        Equiv.symm_apply_apply, Matrix.map_apply] <;> simp [dbl]
  let G : GL (Fin (n + n)) (AF F ⊗[F] E) :=
    ⟨H.submatrix finSumFinEquiv.symm finSumFinEquiv.symm, H'.submatrix finSumFinEquiv.symm finSumFinEquiv.symm,
      by rw [Matrix.submatrix_mul_equiv, g1, Matrix.submatrix_one_equiv],
      by rw [Matrix.submatrix_mul_equiv, g2, Matrix.submatrix_one_equiv]⟩
  have hG : G ∈ HR (AF F) σ (dblG JT) := by
    show ((H.map (cAF σ))ᵀ).submatrix finSumFinEquiv.symm finSumFinEquiv.symm *
      JR (F := F) (AF F) (dblG JT) *
      H.submatrix finSumFinEquiv.symm finSumFinEquiv.symm = JR (F := F) (AF F)
        (dblG JT)
    rw [eJ, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, g3]
  obtain ⟨h, m1, m2⟩ : ∃ h : GAF σ (dblG JT),
      mtF σ _ h = H.submatrix finSumFinEquiv.symm finSumFinEquiv.symm ∧
      mtF σ _ h⁻¹ = H'.submatrix finSumFinEquiv.symm finSumFinEquiv.symm := ⟨⟨G, hG⟩, rfl, rfl⟩
  have sub : ∀ (X : Matrix (Fin n ⊕ Fin n) (Fin n) (AEF F E)) (Y : Matrix (Fin n) (Fin n) (AEF F E)),
      (X * Y).submatrix (finSumFinEquiv (m := n) (n := n)).symm id = X.submatrix finSumFinEquiv.symm id * Y :=
    fun X Y => rfl
  have e1 : e * e = e := he.1
  have e2 : e * cAF σ e = 0 := he.2.1
  have e3 : cAF σ e * cAF σ e = cAF σ e := by rw [← RingHom.map_mul, e1]
  have hd : (1 - (e + cAF σ e)) * (t.1.det - 1) = 0 :=
    GlobalTheory.SplitDetCharF.mul_det_sub_one _ _ fun i j => by rw [sub_mul, one_mul, ht i j, sub_self]
  refine ⟨h, ?_, ?_, ⟨M, hM, fun nS y => ?_⟩,
    GlobalTheory.SplitDetCharF.cutDet σ _ e e1 h, ?_, fun χ m hχ => ?_⟩
  · rw [m1, dC, Matrix.submatrix_mul_equiv, ← sub]
    exact congrArg (fun X => Matrix.submatrix X finSumFinEquiv.symm id) g4
  · intro i j
    rw [m1, ← Matrix.submatrix_one_equiv (finSumFinEquiv (m := n) (n := n)).symm]
    exact congrFun (congrFun g5 (finSumFinEquiv.symm i)) (finSumFinEquiv.symm j)
  · rw [m2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, aC, Matrix.submatrix_mul_equiv, ← sub]
    exact congrArg (fun X => Matrix.submatrix X finSumFinEquiv.symm id * y) g6
  · exact add_comm _ _
  · let w : (AEF F E)ˣ := Units.map (GlobalTheory.SplitDetCharF.cut (cAF σ e) e3) (Matrix.GeneralLinearGroup.det t)
    let u : (AEF F E)ˣ := Units.map (GlobalTheory.SplitDetCharF.cut e e1) (Matrix.GeneralLinearGroup.det t)
    have hw : (w : AEF F E) = (1 - cAF σ e) + cAF σ e * t.1.det := rfl
    have hu' : (u : AEF F E) = (1 - e) + e * t.1.det := rfl
    have huw : Matrix.GeneralLinearGroup.det t = u * w := by
      refine Units.ext ?_
      rw [Units.val_mul, hw, hu', Matrix.GeneralLinearGroup.val_det_apply]
      linear_combination hd - (t.1.det - 1) ^ 2 * e2
    obtain ⟨w', hw'⟩ : IsUnit (cAF σ (w : AEF F E)) := w.isUnit.map (cAF σ)
    have hx : GlobalTheory.SplitDetCharF.cutDet σ _ e e1 h * w' = u := by
      refine Units.ext ?_
      rw [Units.val_mul, hw', hw, hu', GlobalTheory.SplitDetCharF.cutDet_val, m1, Matrix.det_submatrix_equiv_self,
        RingHom.map_add, RingHom.map_sub, RingHom.map_mul, RingHom.map_one, hcc]
      linear_combination (H.det - 1) * (cAF σ t.1.det - 1) * e1 + e * g7
    have hy := GlobalTheory.SplitDetCharF.char_eq_of_mul_conj hc hχ w'⁻¹ w (by rw [← hw', Units.inv_mul])
    rw [huw, map_mul, ← hy, ← map_mul, ← hx, mul_inv_cancel_right]
end GlobalTheory.SplitLagrF
end

section
open GlobalTheory.LagrTheta (lagrInt)
open GlobalTheory.WeilSchrodinger (thetaTr)
open UpperTheory.TP.W (GoodK)
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
  GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  Formalism.IndefR.DatumF
noncomputable section
namespace GlobalTheory.HeckeSplitBase
theorem heckeChar_eq_one_of_split_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (B : Base F E),
    GoodK σ B → ∀ ν : (AF F ⊗[F] E)ˣ →* Circle, IsHeckeCharF ν →
      (∀ e, IsSplitIdemF σ e → ∀ x : (AF F ⊗[F] E)ˣ, (e + cAF σ e) * ((x : AF F ⊗[F] E) - 1) = (x : AF F ⊗[F] E) - 1 →
        ν x = 1) → ∀ x, ν x = 1 := by
  intro F E _ _ _ _ _ σ B hB ν hν hs
  exact _root_.GlobalTheory.HeckeSplitGen.heckeChar_eq_one_of_split F E σ hB.cm ν hν hs
end GlobalTheory.HeckeSplitBase
end

noncomputable section

open PositivityTheory.ThKW.LeviParabolicGL in
theorem PositivityTheory.ThKW.PhaseFourierInjectivity.levi_k : ∀ (F E :
  Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    GoodK σ B → ∀ (nT : ℕ) (JT : Matrix (Fin nT) (Fin nT) E), IsHermND σ JT →
    ∃ m : GL (Fin nT) (AF F ⊗[F] E) →* GAF σ (dblG JT), Continuous m ∧
      (∀ t,
        mtF σ (dblG JT) (m t) * PositivityTheory.ThKW.ModulusFactorDefinition.dC
        (AF F ⊗[F] E) nT =
        PositivityTheory.ThKW.ModulusFactorDefinition.dC (AF F ⊗[F] E) nT * t.1) ∧
      ∀ a : GL (Fin nT) E, m (Matrix.GeneralLinearGroup.map (incAF F E) a) ∈
        GQF σ (dblG JT) := by
  intro F E _ _ _ _ _ σ B hB n JT hT
  classical
  have hc : IsCMExt F E σ := hB.cm
  have hcc := GlobalTheory.SplitLagrF.cAF_invol hc
  have hccE : ∀ x : E, (σ : E →+* E) ((σ : E →+* E) x) = x := fun x => GlobalTheory.SplitDetCharF.sig_invol hc x
  set rE : E := (2 : E)⁻¹ with hrE
  have hrE2 : 2 * rE = 1 := mul_inv_cancel₀ two_ne_zero
  have hr : 2 * (inclR (F := F) (AF F)) rE = 1 := by
    have := congrArg (inclR (F := F) (AF F)) hrE2
    rwa [map_mul, map_ofNat, map_one] at this
  have hJ : ((JR (F := F) (AF F) JT).map (cAF σ))ᵀ = JR (F := F) (AF F) JT := by
    ext i j
    show (1 : AF F) ⊗ₜ[F] σ (JT j i) = (1 : AF F) ⊗ₜ[F] JT i j
    rw [hT.1]
  have hJE : (JT.map (σ : E →+* E))ᵀ = JT := by
    ext i j
    exact hT.1 i j
  have hu : IsUnit (JR (F := F) (AF F) JT).det := by
    have := ((Ne.isUnit hT.2).map (inclR (F := F) (AF F)))
    rwa [RingHom.map_det] at this
  have huE : IsUnit JT.det := Ne.isUnit hT.2
  have eJ : JR (F := F) (AF F) (dblG JT) =
      (Matrix.fromBlocks (JR (F := F) (AF F) JT) 0 0 (-JR (F := F) (AF F) JT)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm := by
    ext i j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [dblG, JR, Matrix.reindex_apply, Matrix.submatrix_apply,
        Equiv.symm_apply_apply, Matrix.map_apply] <;> simp [dbl]
  have eJE : dblG JT =
      (Matrix.fromBlocks JT 0 0 (-JT)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := rfl
  let mG := leviGL (cAF σ) hr hu
  have hmem : ∀ t, mG t ∈ HR (AF F) σ (dblG JT) := by
    intro t
    have h := leviGL_mem (cAF σ) hcc hr hJ hu t
    rw [← eJ] at h
    exact h
  let m₀ : GL (Fin n) (AF F ⊗[F] E) →* HR (AF F) σ (dblG JT) := mG.codRestrict _
    hmem
  let m : GL (Fin n) (AF F ⊗[F] E) →* GAF σ (dblG JT) :=
    { toFun := fun t => m₀ t
      map_one' := m₀.map_one
      map_mul' := m₀.map_mul }
  have := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  have hcont_c : Continuous (cAF (F := F) (E := E) σ) := GlobalTheory.HeisThetaF.continuous_cAF
  have hL : ∀ (f g : GL (Fin n) (AF F ⊗[F] E) → Matrix (Fin n) (Fin n) (AF F ⊗[F] E)), Continuous f → Continuous g →
      Continuous fun t => (L (cAF σ) (inclR (F := F) (AF F) rE) (JR (F := F) (AF F) JT) (f t) (g t)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm := by
    intro f g hf hg
    refine Continuous.matrix_submatrix ?_ _ _
    simp only [L, sM]
    refine ((continuous_const.matrix_mul ?_).matrix_mul continuous_const)
    refine Continuous.matrix_fromBlocks hf continuous_const continuous_const ?_
    exact (continuous_const.matrix_mul ((hg.matrix_map hcont_c).matrix_transpose)).matrix_mul continuous_const
  have hmG : Continuous mG := by
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · show Continuous fun t : GL (Fin n) (AF F ⊗[F] E) =>
        (L (cAF σ) (inclR (F := F) (AF F) rE) (JR (F := F) (AF F) JT) t.1 (t⁻¹).1).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm
      exact hL _ _ Units.continuous_val Units.continuous_coe_inv
    · show Continuous fun t : GL (Fin n) (AF F ⊗[F] E) =>
        (L (cAF σ) (inclR (F := F) (AF F) rE) (JR (F := F) (AF F) JT) (t⁻¹).1 t.1).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm
      exact hL _ _ Units.continuous_coe_inv Units.continuous_val
  have hm : Continuous m := by
    have : Continuous fun t => (⟨mG t, hmem t⟩ : HR (AF F) σ (dblG JT)) :=
      hmG.subtype_mk _
    exact this
  refine ⟨m, hm, ?_, ?_⟩
  · intro t
    exact leviGL_col (cAF σ) hr hu t
  · intro a
    let a' : GL (Fin n) (AF F ⊗[F] E) := Matrix.GeneralLinearGroup.map (incAF F E) a
    show ((m₀ a' : HR (AF F) σ (dblG JT)) : GL (Fin (n + n)) (AF F ⊗[F] E)) ∈
      HFin (AF F) σ (dblG JT)
    refine ⟨leviGL (σ : E →+* E) hrE2 huE a, ?_, ?_⟩
    · have h := leviGL_mem (σ : E →+* E) hccE hrE2 hJE huE a
      rw [← eJE] at h
      exact h
    · exact leviGL_map (inclR (F := F) (AF F)) (σ : E →+* E) (cAF σ) (fun x => rfl) hrE2 hr huE hu a
end
end

abbrev _root_.GlobalTheory.T.hecke_character_trivial_of_split :=
  GlobalTheory.HeckeSplitBase.heckeChar_eq_one_of_split_k

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
  GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  Formalism.IndefR.DatumF
noncomputable section
namespace PositivityTheory.ThKW.PhaseFourierInjectivity
open PositivityTheory.ThKW.ModulusFactorDefinition
theorem rat_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B :
  Base F E),
    GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT)
      E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle) (ωd : GAF σ JS × GAF σ (dblG JT) →*
            Module.End ℂ (WOF F E nS (nT + nT) → ℂ)),
        IsWeilDatumOF σ JS (dblG JT)
            (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ γ ∈ GQF σ (dblG JT), ∀ t : GL (Fin nT) (AF F ⊗[F] E),
        mtF σ (dblG JT) γ * dC (AF F ⊗[F] E) nT = dC (AF F ⊗[F] E) nT * t.1 →
      ∀ f, IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ f →
        lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT) (ωd (1, γ) f) =
          lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT) f := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ ν 𝓕 hν h𝓕 χS ωd hω γ hγ t ht f hf
  obtain ⟨i1, i2, i3, i4, i5, K, hK,
    hKc⟩ := _root_.GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  have : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  have : Countable (ratLF F E nS nT) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  have h0 : ∀ y : WOF F E nS (nT + nT),
    symplOHF σ JS (dblG JT) ξ₀ 0 y = 0 := fun y => by
    simp [symplOHF, symplOF, hOF]
  have h1 : ∀ w : WOF F E nS nT, ωd (1, γ) f (dC (AF F ⊗[F] E) nT * w) = f (dC (AF F ⊗[F] E) nT * ((t⁻¹).1 * w)) := by
    intro w
    have hact : actOF σ JS _ 1 γ (dC (AF F ⊗[F] E) nT * ((t⁻¹).1 * w)) = dC (AF F ⊗[F] E) nT * w := by
      unfold actOF
      rw [inv_one, show mtF σ JS 1 = 1 from rfl, Matrix.mul_one, ← Matrix.mul_assoc, ht, Matrix.mul_assoc,
        ← Matrix.mul_assoc t.1, Units.mul_inv, Matrix.one_mul]
    have h2 := congrFun (hω.om_heis 1 γ (dC (AF F ⊗[F] E) nT * ((t⁻¹).1 * w)) f hf) 0
    rw [hω.om_aut 1 (one_mem _) γ hγ _ (GlobalTheory.HeisThetaF.isThetaFunOF_heisOF_k F E σ B hB _ _ JS _ ξ₀ _ f
      hf), hact] at h2
    simp only [heisOF, h0, AddChar.map_zero_eq_one, one_mul, zero_add] at h2
    exact h2.symm
  obtain ⟨g₀, -, hg⟩ := hγ
  have hg' : mtF σ _ γ = g₀.1.map (incAF F E) := (congrArg Units.val hg).symm
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : Matrix (Fin nT) (Fin nT) E, t.1 = incM F s₀ := by
    refine ⟨(g₀.1 * GlobalTheory.LagrThetaInv.dC E nT).submatrix (fun p => finSumFinEquiv (Sum.inl p)) id, ?_⟩
    have e : (g₀.1 * GlobalTheory.LagrThetaInv.dC E nT).map (incAF F E) = dC (AF F ⊗[F] E) nT * t.1 := by
      rw [Matrix.map_mul, ← hg', ← ht]
      congr 1
      have := GlobalTheory.LagrThetaInv.dC_mul_rat (F := F) (1 : Matrix (Fin nT) (Fin nT) E)
      rw [Matrix.mul_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at this
      exact this.symm
    ext i j
    rw [← GlobalTheory.LagrThetaInv.dC_mul_inl t.1, ← e]
    rfl
  have hd := GlobalTheory.DiagThetaRatF.det_ne_zero_of_unit t s₀ hs₀
  have hs₁ : (t⁻¹).1 = incM F s₀⁻¹ := by
    rw [Matrix.coe_units_inv]
    refine Matrix.inv_eq_right_inv ?_
    rw [hs₀]
    show s₀.map (inclR (F := F) (AF F)) * s₀⁻¹.map (inclR (F := F) (AF F)) = 1
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hd),
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hm : ∀ (s : Matrix (Fin nT) (Fin nT) E) (x : WOF F E nS nT), x ∈ ratLF F E nS nT →
      (incM F s * x : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)) ∈ ratLF F E nS nT := by
    rintro s _ ⟨y, rfl⟩
    refine ⟨s * y, ?_⟩
    show (s * y).map (incAF F E) = s.map (incAF F E) * y.map (incAF F E)
    exact Matrix.map_mul
  let e : WOF F E nS nT ≃+ WOF F E nS nT :=
    { toFun := fun w => (t⁻¹).1 * w
      invFun := fun w => t.1 * w
      left_inv := fun w => by simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      right_inv := fun w => by simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      map_add' := fun v w => Matrix.mul_add _ v w }
  unfold lagrInt
  simp only [h1]
  exact GlobalTheory.DiagThetaRatF.setIntegral_comp_aut (ratLF F E nS nT) hK hKc ν h𝓕 e
    (continuous_const.matrix_mul continuous_id) (continuous_const.matrix_mul continuous_id)
    (fun x hx => by
      show (t⁻¹).1 * x ∈ _
      rw [hs₁]
      exact hm _ x hx)
    (fun x hx => by
      show t.1 * x ∈ _
      rw [hs₀]
      exact hm _ x hx)
    (fun w => f (dC (AF F ⊗[F] E) nT * w)) (periodic hf)
end PositivityTheory.ThKW.PhaseFourierInjectivity
end
end

abbrev _root_.GlobalTheory.T.lagrangian_darboux_schrodinger_action :=
  GlobalTheory.LagrUniq.lagr_invariant_unique_k

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
  GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  Formalism.IndefR.DatumF
noncomputable section
open GlobalTheory.SplitLagrF in
theorem PositivityTheory.ThKW.fundamental_domain_parseval_global : ∀ (F E :
  Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT)
      E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle) (ωd : GAF σ JS × GAF σ (dblG JT) →*
            Module.End ℂ (WOF F E nS (nT + nT) → ℂ)),
        IsWeilDatumOF σ JS (dblG JT)
            (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ α : GL (Fin nT) (AF F ⊗[F] E) →* Circle,
        (∀ (h : GAF σ (dblG JT)) (t : GL (Fin nT) (AF F ⊗[F] E)),
          mtF σ (dblG JT) h * ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT)
            (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) = ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT)
            (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * t.1 →
          ∀ f, IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ f →
            lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F]
              E)).submatrix finSumFinEquiv.symm id) (ωd (1,
              h) f) = (α t : ℂ) * ((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F)
              (Matrix.GeneralLinearGroup.det t)) : ℝ) ^ ((Fintype.card (Fin nS) : ℝ) / 2) : ℝ) : ℂ) *
              lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F]
              E)).submatrix finSumFinEquiv.symm id) f) →
      ∀ f₀, IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ f₀ →
        lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F]
          E)).submatrix finSumFinEquiv.symm id) f₀ ≠ 0 →
      ∀ e, IsSplitIdemF σ e → ∀ t : GL (Fin nT) (AF F ⊗[F] E),
        (∀ i j, (e + cAF σ e) * (t.1 - 1) i j = (t.1 - 1) i j) → α t = χS (Matrix.GeneralLinearGroup.det t) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 χS ωd hωd α hlaw f₀ hf₀ hne e he t ht
  obtain ⟨h, hhC, hsupp, ⟨M, hM, hMy⟩, x, hx,
    hχx⟩ := GlobalTheory.SplitLagrF.exists_levi_k F E σ B hB nT JT hT e he t ht
  obtain ⟨ℓ, hinv, ⟨f, hf, hℓf⟩,
    hcmp⟩ := GlobalTheory.SplitLagrF.exists_form_k F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 e he f₀ hf₀
    hne
  obtain ⟨R, hR, hRk⟩ := hcmp M hM
  obtain ⟨r, hr, hsp⟩ := hωd.om_split e he 1 h (suppAtF_one σ e JS) hsupp 1 x (isDetAtF_one σ e JS) hx
  set m : ℝ := (((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F)
    (Matrix.GeneralLinearGroup.det t)) : ℝ) ^ ((Fintype.card (Fin nS) : ℝ) / 2) : ℝ) with hm_def
  have hm : 0 < m := Real.rpow_pos_of_pos (modu_pos _) _
  have h1 := hsp ℓ hinv f hf
  have h2 : ℓ (ωd (1, h) f) = (R : ℂ) * ((α t : ℂ) * (m : ℂ)) * ℓ f := by
    refine hRk f (ωd (1, h) f) _ hf (hωd.om_pres _ f hf) (fun y _ => ?_)
    have hth : IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ
        (heisOF σ JS (dblG JT) ξ₀ B.ψ (aC F E nT * (M * y)) f) :=
      GlobalTheory.HeisThetaF.isThetaFunOF_heisOF_k F E σ B hB nS (nT + nT) JS _ ξ₀ _ f hf
    have hh := hωd.om_heis 1 h (aC F E nT * (M * y)) f hf
    have hact : actOF σ JS (dblG JT) 1 h (aC F E nT * (M * y)) = aC F E nT * y
      := by
      unfold actOF
      rw [← hMy nS y, ← Matrix.mul_assoc, ← GlobalTheory.WeilPartsF.mtF_mul, mul_inv_cancel, inv_one]
      simp only [mtF_one', Matrix.one_mul, Matrix.mul_one]
    unfold prof
    rw [← hact, ← hh]
    exact hlaw h t hhC _ hth
  have h3 : (R : ℂ) * ((α t : ℂ) * (m : ℂ)) = (r : ℂ) * (χS x : ℂ) := by
    have := h2.symm.trans h1
    simp only [splitFacOF, MonoidHom.one_apply, inv_one, one_mul] at this
    exact mul_right_cancel₀ hℓf this
  have hu : α t * (χS x)⁻¹ = 1 := by
    apply circle_eq_one_of_pos (t := r / (R * m)) (div_pos hr (mul_pos hR hm))
    have hx0 : ((χS x : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
    have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
    have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    rw [Circle.coe_mul, Circle.coe_inv]
    push_cast
    field_simp
    linear_combination h3
  rw [← hχx χS nS hωd.resS]
  exact mul_inv_eq_one.mp hu
end
end

abbrev _root_.GlobalTheory.T.fundamental_domain_haar_parseval :=
  PositivityTheory.ThKW.fundamental_domain_parseval_global

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
  GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  Formalism.IndefR.DatumF
open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.LagrangianIntegralFactorisation in
theorem PositivityTheory.ThKW.fundamental_domain_plancherel_global : ∀ (F E :
  Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT)
      E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle) (ωd : GAF σ JS × GAF σ (dblG JT) →*
            Module.End ℂ (WOF F E nS (nT + nT) → ℂ)),
        IsWeilDatumOF σ JS (dblG JT)
            (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∃ α : GL (Fin nT) (AF F ⊗[F] E) →* Circle, Continuous α ∧
        (∀ a : GL (Fin nT) E, α (Matrix.GeneralLinearGroup.map (incAF F E) a) = 1) ∧
        ∀ (h : GAF σ (dblG JT)) (t : GL (Fin nT) (AF F ⊗[F] E)),
          mtF σ (dblG JT) h * ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT)
            (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) = ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT)
            (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * t.1 →
          ∀ f, IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ f →
            lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F]
              E)).submatrix finSumFinEquiv.symm id) (ωd (1,
              h) f) = (α t : ℂ) * ((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F)
              (Matrix.GeneralLinearGroup.det t)) : ℝ) ^ ((Fintype.card (Fin nS) : ℝ) / 2) : ℝ) : ℂ) *
              lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F]
              E)).submatrix finSumFinEquiv.symm id) f := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 χS ωd hωd
  obtain ⟨m, hmc, hmC, hmr⟩ := PositivityTheory.ThKW.PhaseFourierInjectivity.levi_k F E σ B hB nT JT hT
  obtain ⟨α, hαc, hαq, hlaw⟩ := core (V := WOF F E nS (nT + nT) → ℂ)
    (IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ)
    (fun a b f g hf hg => GlobalTheory.WeilPartsF.theta_add (GlobalTheory.WeilPartsF.theta_smul a hf)
      (GlobalTheory.WeilPartsF.theta_smul b hg))
    (ωd.comp (MonoidHom.inr _ _)) (fun h f hf => hωd.om_pres _ f hf)
    (lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT))
    (fun a b f g hf hg => lagrInt_lin ν 𝓕 f g a b
      (PositivityTheory.ThKW.PhaseFourierInjectivity.integrable F E σ nS nT JS JT ξ₀ B.ψ ν 𝓕 hν h𝓕 f hf)
        (PositivityTheory.ThKW.PhaseFourierInjectivity.integrable F E σ nS nT JS JT ξ₀ B.ψ ν 𝓕 hν h𝓕 g hg))
    (fun h t => mtF σ (dblG JT) h * dC (AF F ⊗[F] E) nT = dC (AF F ⊗[F] E) nT *
      t.1)
    (fun a b s u ha hb => by
      show mtF σ _ (a * b) * _ = _ * (s * u).1
      rw [GlobalTheory.WeilPartsF.mtF_mul, Matrix.mul_assoc, hb, ← Matrix.mul_assoc, ha, Matrix.mul_assoc, Units.val_mul])
    (fun a s ha => by
      show mtF σ _ a⁻¹ * _ = _ * (s⁻¹).1
      have e : dC (AF F ⊗[F] E) nT = mtF σ _ a⁻¹ * (dC (AF F ⊗[F] E) nT * s.1) := by
        rw [← ha, ← Matrix.mul_assoc, mtF_inv_mul, Matrix.one_mul]
      calc mtF σ _ a⁻¹ * dC (AF F ⊗[F] E) nT
          = mtF σ _ a⁻¹ * (dC (AF F ⊗[F] E) nT * (s.1 * (s⁻¹).1)) := by
            rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
        _ = mtF σ _ a⁻¹ * (dC (AF F ⊗[F] E) nT * s.1) * (s⁻¹).1 := by
            simp only [Matrix.mul_assoc]
        _ = dC (AF F ⊗[F] E) nT * (s⁻¹).1 := by rw [← e])
    (mfac F E nS) (mfac_one nS) (mfac_pos nS) (mfac_mul nS)
    (fun h t hr f hf => PositivityTheory.ThKW.PhaseFourierInjectivity.norm_law_k F E σ B hB nS nT JS JT hS hT ξ₀
      hξ₀ hσ ν 𝓕 hν h𝓕 χS ωd hωd h t hr f hf)
    m hmc hmC
    (fun f hf => PositivityTheory.ThKW.PhaseFourierInjectivity.cont_k F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕
      hν h𝓕 χS ωd hωd f hf)
    (GQF σ (dblG JT) : Set _)
    (fun γ hγ t hr f hf => PositivityTheory.ThKW.PhaseFourierInjectivity.rat_k F E σ B hB nS nT JS JT hS hT ξ₀
      hξ₀ hσ ν 𝓕 hν h𝓕 χS ωd hωd γ hγ t hr f hf)
    (fun k hk => by
      obtain ⟨M, t, h1, h2⟩ := PositivityTheory.ThKW.PhaseFourierInjectivity.conj_pow F E σ nT JT hT k hk
      exact ⟨M, t, h1, fun n hn => h2 n (by rw [Units.val_one, Matrix.mul_one] at hn; exact hn)⟩)
  exact ⟨α, hαc, fun a => hαq _ (hmr a), fun h t hr f hf => hlaw h t hr f hf⟩
end

abbrev _root_.GlobalTheory.T.fundamental_domain_haar_plancherel :=
  PositivityTheory.ThKW.fundamental_domain_plancherel_global

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
  GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  Formalism.IndefR.DatumF
noncomputable section
namespace GlobalTheory.SiegelLawDblTargetF
theorem lagr_law_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B
  : Base F E),
    GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT)
      E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle) (ωd : GAF σ JS × GAF σ (dblG JT) →*
            Module.End ℂ (WOF F E nS (nT + nT) → ℂ)),
        IsWeilDatumOF σ JS (dblG JT)
            (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ (h : GAF σ (dblG JT)) (t : GL (Fin nT) (AF F ⊗[F] E)),
          mtF σ (dblG JT) h * ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT)
            (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) = ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT)
            (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * t.1 →
          ∀ f, IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ f →
            lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F]
              E)).submatrix finSumFinEquiv.symm id) (ωd (1,
              h) f) = (χS (Matrix.GeneralLinearGroup.det t) : ℂ) * ((((adeleClass F).modu (Units.map (Algebra.norm (AF
              F) : AF F ⊗[F] E →* AF F) (Matrix.GeneralLinearGroup.det t)) : ℝ) ^ ((Fintype.card (Fin nS) : ℝ) / 2) : ℝ)
              : ℂ) * lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F
              ⊗[F] E)).submatrix finSumFinEquiv.symm id) f := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 χS ωd hωd
  obtain ⟨α, hαc, hαr,
    hlaw⟩ := GlobalTheory.T.fundamental_domain_haar_plancherel F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕
    χS ωd hωd
  intro h t hht f hf
  by_cases h0 : ∀ g, IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ g →
      lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F]
        E)).submatrix finSumFinEquiv.symm id) g = 0
  · rw [h0 _ (hωd.om_pres _ f hf), h0 f hf, mul_zero]
  push Not at h0
  obtain ⟨f₀, hf₀, hne⟩ := h0
  have hsp := GlobalTheory.T.fundamental_domain_haar_parseval F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 χS
    ωd hωd α hlaw f₀ hf₀ hne
  have hα : ∀ a : GL (Fin nT) (AF F ⊗[F] E), α a = χS (Matrix.GeneralLinearGroup.det a) := by
    rcases Nat.eq_zero_or_pos nT with hn0 | hpos
    · intro a
      have hd : Matrix.GeneralLinearGroup.det a = 1 := by
        ext; rw [Matrix.GeneralLinearGroup.val_det_apply]; subst hn0; simp
      rw [char_det_one F E nT α a hd, hd, map_one]
    obtain ⟨i0⟩ : Nonempty (Fin nT) := ⟨⟨0, hpos⟩⟩
    have hhec : IsHeckeCharF (α.comp (GlobalTheory.LeviOrigin.dgU nT i0) * χS⁻¹) := by
      refine ⟨?_, ?_⟩
      · exact (hαc.comp (GlobalTheory.LeviOrigin.continuous_dgU nT i0)).mul (hωd.hecS.1.inv)
      · intro x
        rw [MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.inv_apply, hωd.hecS.2 x, inv_one, mul_one,
          GlobalTheory.LeviOrigin.dgU_map (incAF F E) nT i0 x]
        exact hαr _
    have hν1 := GlobalTheory.T.hecke_character_trivial_of_split F E σ B hB _ hhec (by
      intro e he x hx
      have h2 := hsp e he (GlobalTheory.LeviOrigin.dgU nT i0 x) (by
        intro k l
        rw [GlobalTheory.LeviOrigin.dgU_sub_one]
        split_ifs
        · exact hx
        · exact mul_zero _)
      rw [MonoidHom.mul_apply, MonoidHom.comp_apply, h2, GlobalTheory.LeviOrigin.det_dgU, MonoidHom.inv_apply,
        mul_inv_cancel])
    have hdg : ∀ x, α (GlobalTheory.LeviOrigin.dgU nT i0 x) = χS x := by
      intro x
      have := hν1 x
      rw [MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.inv_apply] at this
      exact mul_inv_eq_one.mp this
    intro a
    have hb : Matrix.GeneralLinearGroup.det (a * (GlobalTheory.LeviOrigin.dgU nT i0 (Matrix.GeneralLinearGroup.det
      a))⁻¹) = 1 := by
      rw [map_mul, map_inv, GlobalTheory.LeviOrigin.det_dgU, mul_inv_cancel]
    have h3 : α a = α (a * (GlobalTheory.LeviOrigin.dgU nT i0 (Matrix.GeneralLinearGroup.det a))⁻¹) *
        α (GlobalTheory.LeviOrigin.dgU nT i0 (Matrix.GeneralLinearGroup.det a)) := by
      rw [← map_mul, inv_mul_cancel_right]
    rw [h3, char_det_one F E nT α _ hb, one_mul]
    exact hdg _
  rw [hlaw h t hht f hf, hα t]
theorem main_law_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B
  : Base F E),
    GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT)
      E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : Darboux (symp (cA σ) ξ (incM F (dblG JT)ᵀ) (incM F JB)) κ),
        (∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : κ → F,
          co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle),
        IsHeckeCharF χS → ResEtaF χS nS →
      ∀ ωd : GAF σ JS × GAF σ
        (dblG JT) →*
            Module.End ℂ (WOF F E nS (nT + nT) → ℂ),
          IsWeilDatumOF σ JS (dblG JT)
            (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ omp : UG (cA σ) (incM F (dblG JT)ᵀ) × UG (cA σ) (incM F JB) →*
            Module.End ℂ ((κ → AF F) → ℂ),
          GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ωd omp →
      ∀ (p : UG (cA σ) (incM F (dblG JT)ᵀ)) (t : GL (Fin nT) (AF F ⊗[F] E)),
        p.1.1 * ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id)
          = ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) *
          t.1 →
      ∀ Φ ∈ schA F κ, omp (p, 1) Φ ∈ schA F κ ∧
        lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F]
          E)).submatrix finSumFinEquiv.symm id) (thetaTr F co B.ψ (omp (p, 1) Φ)) =
          (χS (Matrix.GeneralLinearGroup.det t) : ℂ) *
            ((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F)
              (Matrix.GeneralLinearGroup.det t)) : ℝ) ^ ((Fintype.card (Fin nS) : ℝ) / 2) : ℝ) : ℂ) *
            lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F]
              E)).submatrix finSumFinEquiv.symm id) (thetaTr F co B.ψ Φ) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ JB ξ hξ κ _ co hco ν 𝓕 hν h𝓕 χS hχS rχS ωd hωd omp htr p t hpt
    Φ hΦ
  obtain ⟨h, hh⟩ := exists_gaf σ (dblG JT) p
  have hg : mtF σ JS 1 = ((1 : UG (cA σ) (incM F JB))⁻¹).1.1ᵀ := by
    simp only [mtF, map_one, inv_one]; simp
  obtain ⟨hmem, heq⟩ := htr p 1 1 h hh hg Φ hΦ
  refine ⟨hmem, ?_⟩
  erw [heq]
  have hth := GlobalTheory.TransportHeisF.isThetaFunOF_thetaTr_k F E σ B hB nS (nT + nT) JS
    (dblG JT) hS (GlobalTheory.WeilSchrodinger.DblTargetF.isHermND_dblG hT) ξ₀
      hξ₀ hσ hωd.std _ JB ξ
    rfl hξ κ co hco Φ hΦ
  exact lagr_law_k F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 χS ωd hωd h t (by rw [hh]; exact hpt) _ hth
end GlobalTheory.SiegelLawDblTargetF
end
end

abbrev _root_.GlobalTheory.T.lagrangian_darboux_schrodinger_unitary :=
  GlobalTheory.SiegelLawDblTargetF.main_law_k

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
  GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  Formalism.IndefR.DatumF
noncomputable section
theorem GlobalTheory.WeilSchrodinger.DblTargetF.siegelRule_dblTarget_k : ∀ (F E :
  Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT)
      E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle),
        IsHeckeCharF χS → ResEtaF χS nS →
      ∀ (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : Darboux (symp (cA σ) ξ (incM F (dblG JT)ᵀ) (incM F JB)) κ),
        (∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : κ → F,
          co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
        ∀ ωd : GAF σ JS × GAF σ
          (dblG JT) →*
            Module.End ℂ (WOF F E nS (nT + nT) → ℂ),
          IsWeilDatumOF σ JS (dblG JT)
            (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
        ∀ omp : UG (cA σ) (incM F (dblG JT)ᵀ) × UG (cA σ) (incM F JB) →*
            Module.End ℂ ((κ → AF F) → ℂ),
          GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ωd omp →
          SiegelRule (cA σ) (adeleClass F) B.ψ ξ (incM F JB) (incM F (dblG JT)ᵀ)
            (GlobalTheory.WeilSchrodinger.transD (cA σ) co) χS
            ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id)
            (omp.comp (MonoidHom.inl _ _)) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ χS hχS rχS JB ξ hξ κ _ co hco ωd hωd omp htr
    l hl hinv p t hpt φ hφ
  obtain ⟨ν, 𝓕, hν, h𝓕⟩ := GlobalTheory.TowerFD.exists_fd_any F E nS nT
  obtain ⟨c,
    hc⟩ := GlobalTheory.T.lagrangian_darboux_schrodinger_action F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ JB ξ hξ κ
    co hco ν 𝓕 hν h𝓕 l hl hinv
  obtain ⟨hmem,
    hrule⟩ := GlobalTheory.T.lagrangian_darboux_schrodinger_unitary F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ JB ξ
    hξ κ co hco ν 𝓕 hν h𝓕 χS hχS rχS
    ωd hωd omp htr p t hpt φ hφ
  show l (omp (p, 1) φ) = _
  rw [hc _ hmem, hrule, hc _ hφ]
  ring
end
end

abbrev _root_.GlobalTheory.T.splitting_character_restricted_eta :=
  GlobalTheory.WeilSchrodinger.DblTargetF.siegelRule_dblTarget_k
end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SplittingCharacterRestrictedEta =====
