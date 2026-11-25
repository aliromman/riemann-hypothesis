module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.Matrix.Normed
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GrpParts
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ExistsLieCompl
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GrpHaarW
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ExpProdSt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PlaceCh
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PsiInv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.UniInf
import Mathlib.Tactic.Linter.HaveILetI
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Linter.Style
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GrpInj

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PlaceV, Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.BlockEmb, Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GaugeVolU, Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.BlockEx, Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GrpTop, Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.BlockGrp

-- ===== clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PlaceV =====
-- clump-header: {"m": "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PlaceV", "h": "module\n\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PlaceCh\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ExpProdSt\nimport Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GrpInj\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PsiInv\nimport Mathlib.Tactic.Linter.Style\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric Set Formalism.MainNotions.S Formalism.MainNotions.S.Gauge
open scoped Matrix

section Coords

variable {n : ℕ}

def rlM (n : ℕ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] EuclideanSpace ℝ (Fin n × Fin n × Bool) where
  toFun X := (WithLp.equiv 2 _).symm (realifyFun X)
  map_add' X Y := by
    ext p
    simp only [realifyFun, WithLp.equiv_symm_apply, PiLp.add_apply, Matrix.add_apply]
    split_ifs <;> simp
  map_smul' c X := by
    ext p
    simp only [realifyFun, WithLp.equiv_symm_apply, PiLp.smul_apply, Matrix.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

def urM (n : ℕ) : EuclideanSpace ℝ (Fin n × Fin n × Bool) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun x := unrealify x
  map_add' x y := by
    ext i j
    apply Complex.ext <;> simp [unrealify]
  map_smul' c x := by
    ext i j
    apply Complex.ext <;> simp [unrealify]

theorem ur_rl (X : Matrix (Fin n) (Fin n) ℂ) : urM n (rlM n X) = X := _root_.Formalism.MainNotions.S.Gauge.unrealify_realify X

theorem rl_ur (x : EuclideanSpace ℝ (Fin n × Fin n × Bool)) : rlM n (urM n x) = x := by
  ext ⟨i, j, b⟩
  cases b <;> simp [rlM, urM, realifyFun, unrealify]

theorem frob_ur (x : EuclideanSpace ℝ (Fin n × Fin n × Bool)) : frob (urM n x) = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  unfold frob
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool, Complex.sq_norm, Complex.normSq_apply]
  simp [urM, unrealify, Real.norm_eq_abs, sq]
  ring

def subC (ε : Fin n → Bool) (S : Finset (Fin n)) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {M | InCompl ε S M}
  zero_mem' := ⟨by simp, fun _ _ _ _ => rfl⟩
  add_mem' := by
    intro A B hA hB
    refine ⟨?_, fun i hi j hj => ?_⟩
    · rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
      have := congrArg₂ (· + ·) hA.1 hB.1
      simp only [add_zero] at this
      rw [← this]; abel
    · show A i j + B i j = 0
      rw [hA.2 i hi j hj, hB.2 i hi j hj, add_zero]
  smul_mem' := by
    intro c A hA
    refine ⟨?_, fun i hi j hj => ?_⟩
    · show (c • A)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * (c • A) = 0
      rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hA.1, smul_zero]
    · show c • A i j = 0
      rw [hA.2 i hi j hj, smul_zero]

def subB (ε : Fin n → Bool) (S : Finset (Fin n)) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {M | InBlock ε S M}
  zero_mem' := ⟨by simp, fun _ _ _ => rfl⟩
  add_mem' := by
    intro A B hA hB
    refine ⟨?_, fun i j hij => ?_⟩
    · rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
      have := congrArg₂ (· + ·) hA.1 hB.1
      simp only [add_zero] at this
      rw [← this]; abel
    · show A i j + B i j = 0
      rw [hA.2 i j hij, hB.2 i j hij, add_zero]
  smul_mem' := by
    intro c A hA
    refine ⟨?_, fun i j hij => ?_⟩
    · show (c • A)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * (c • A) = 0
      rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hA.1, smul_zero]
    · show c • A i j = 0
      rw [hA.2 i j hij, smul_zero]

def blk (S : Finset (Fin n)) (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => if i ∈ S ∧ j ∈ S then X i j else 0

theorem lie_entry (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X) i j =
      star (X j i) * (if ε j then 1 else -1) + (if ε i then 1 else -1) * X i j := by
  simp [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]

theorem blk_lie (ε : Fin n → Bool) (S : Finset (Fin n)) (X : Matrix (Fin n) (Fin n) ℂ)
    (hX : Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0) :
    (blk S X)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * blk S X = 0 := by
  ext i j
  have h := congrFun (congrFun hX i) j
  rw [lie_entry] at h ⊢
  by_cases hij : i ∈ S ∧ j ∈ S
  · have hji : j ∈ S ∧ i ∈ S := ⟨hij.2, hij.1⟩
    simp only [blk, ite_eq_left hij, ite_eq_left hji]
    simpa using h
  · have hji : ¬ (j ∈ S ∧ i ∈ S) := fun h' => hij ⟨h'.2, h'.1⟩
    simp [blk, ite_eq_right hij, ite_eq_right hji]

end Coords

section Split

variable {n : ℕ}

theorem sup_eq_gLie (ε : Fin n → Bool) (S : Finset (Fin n)) :
    (subC ε S).map (rlM n) ⊔ (subB ε S).map (rlM n) = gLie ε := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · rintro _ ⟨X, hX, rfl⟩
      exact skewLie_holds n ε X hX.1
    · rintro _ ⟨X, hX, rfl⟩
      exact skewLie_holds n ε X hX.1
  · intro x hx
    set X := urM n x with hXd
    have hXl : Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0 := lieSkew_holds n ε x hx
    have hb : blk S X ∈ subB ε S := by
      refine ⟨blk_lie ε S X hXl, fun i j hij => ?_⟩
      have : ¬ (i ∈ S ∧ j ∈ S) := by tauto
      simp [blk, this]
    have hc : X - blk S X ∈ subC ε S := by
      refine ⟨?_, fun i hi j hj => ?_⟩
      · rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, sub_add_sub_comm, hXl, blk_lie ε S X hXl,
          sub_zero]
      · show X i j - blk S X i j = 0
        simp [blk, hi, hj]
    have e : x = rlM n (X - blk S X) + rlM n (blk S X) := by
      rw [← map_add (f := _), sub_add_cancel, hXd, rl_ur]
    rw [e]
    exact Submodule.add_mem_sup (Submodule.mem_map_of_mem hc) (Submodule.mem_map_of_mem hb)

theorem orth_CB (ε : Fin n → Bool) (S : Finset (Fin n)) :
    ∀ x ∈ (subC ε S).map (rlM n), ∀ y ∈ (subB ε S).map (rlM n), inner ℝ x y = 0 := by
  rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  refine Finset.sum_eq_zero fun p _ => ?_
  obtain ⟨i, j, b⟩ := p
  by_cases hij : i ∈ S ∧ j ∈ S
  · have h0 : A i j = 0 := hA.2 i hij.1 j hij.2
    cases b <;> simp [rlM, realifyFun, h0]
  · have h0 : B i j = 0 := hB.2 i j (by tauto)
    cases b <;> simp [rlM, realifyFun, h0]

end Split

section Chart

variable {n : ℕ}

theorem exp_blk_mul_proj (S : Finset (Fin n)) (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : ∀ i j, (i ∉ S ∨ j ∉ S) → M i j = 0) :
    NormedSpace.exp M * Matrix.diagonal (fun k => if k ∈ S then (0 : ℂ) else 1) =
      Matrix.diagonal (fun k => if k ∈ S then (0 : ℂ) else 1) := by
  apply exp_mul_of_mul_eq_zero
  ext a b
  rw [Matrix.mul_diagonal]
  by_cases hb : b ∈ S
  · simp [hb]
  · simp [hb, hM a b (Or.inr hb)]

theorem chart_injOn {α β : Type} [Fintype α] [Fintype β] (ε : Fin n → Bool) (S : Finset (Fin n))
    (L₀ : EuclideanSpace ℝ α →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ) (L₁ : EuclideanSpace ℝ β →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ)
    (h3 : ∀ z, InCompl ε S (L₀ z)) (h4 : ∀ z, frob (L₀ z) = ‖z‖ ^ 2)
    (h7 : ∀ z, InBlock ε S (L₁ z)) (h8 : ∀ z, frob (L₁ z) = ‖z‖ ^ 2) :
    ∃ r : ℝ, 0 < r ∧ Set.InjOn (fun z : EuclideanSpace ℝ α × EuclideanSpace ℝ β =>
      expU ε (L₀ z.1) * expU ε (L₁ z.2)) (ball 0 r) := by
  set P := Matrix.diagonal (fun k => if k ∈ S then (0 : ℂ) else 1) with hP
  have hz : ∀ {γ : Type} [Fintype γ] (L' : EuclideanSpace ℝ γ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ),
      (∀ z, frob (L' z) = ‖z‖ ^ 2) → ∀ x, L' x = 0 → x = 0 := by
    intro γ _ L' hn x hx
    have := hn x
    rw [hx] at this
    simp only [frob, Matrix.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Finset.sum_const_zero] at this
    exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this.symm)
  obtain ⟨r1, hr1, hi1⟩ := exp_mul_injOn (V := Unit) (LinearMap.pi fun _ => L₀) (fun _ => P) fun x hx =>
    hz L₀ h4 x (lie_zero_of_cols ε S _ (h3 x).1 (h3 x).2 (hx ()))
  obtain ⟨r2, hr2, hi2⟩ := exp_mul_injOn (V := Unit) (LinearMap.pi fun _ => L₁) (fun _ => 1) fun x hx =>
    hz L₁ h8 x (by simpa using hx ())
  refine ⟨min r1 r2, lt_min hr1 hr2, fun z hz' z' hz'' he => ?_⟩
  have hb1 : ∀ p : EuclideanSpace ℝ α × EuclideanSpace ℝ β, p ∈ ball 0 (min r1 r2) → p.1 ∈ ball 0 r1 ∧ p.2 ∈ ball 0 r2 := by
    intro p hp
    rw [mem_ball_zero_iff, Prod.norm_def] at hp
    exact ⟨mem_ball_zero_iff.2 ((le_max_left _ _).trans_lt (hp.trans_le (min_le_left _ _))),
      mem_ball_zero_iff.2 ((le_max_right _ _).trans_lt (hp.trans_le (min_le_right _ _)))⟩

  have hm : NormedSpace.exp (L₀ z.1) * NormedSpace.exp (L₁ z.2) =
      NormedSpace.exp (L₀ z'.1) * NormedSpace.exp (L₁ z'.2) := by
    have := congrArg (fun g : Formalism.REAL.UJ ε => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) he
    simp only [Subgroup.coe_mul, Units.val_mul] at this
    rwa [expU_val _ _ (h3 z.1).1, expU_val _ _ (h7 z.2).1, expU_val _ _ (h3 z'.1).1,
      expU_val _ _ (h7 z'.2).1] at this
  have hblk : ∀ y, ∀ i j, (i ∉ S ∨ j ∉ S) → (-L₁ y) i j = 0 := fun y i j hij => by
    simp [(h7 y).2 i j hij]
  have hx : z.1 = z'.1 := by
    apply hi1 (hb1 z hz').1 (hb1 z' hz'').1
    funext u
    show NormedSpace.exp (L₀ z.1) * P = NormedSpace.exp (L₀ z'.1) * P
    have e1 : NormedSpace.exp (L₀ z.1) =
        NormedSpace.exp (L₀ z'.1) * NormedSpace.exp (L₁ z'.2) * NormedSpace.exp (-L₁ z.2) := by
      rw [← hm, Matrix.mul_assoc, Formalism.REAL.matrix_exp_mul_exp_neg, Matrix.mul_one]
    rw [e1, Matrix.mul_assoc, Matrix.mul_assoc, exp_blk_mul_proj S _ (hblk z.2), exp_blk_mul_proj S _ (h7 z'.2).2]
  have hy : z.2 = z'.2 := by
    apply hi2 (hb1 z hz').2 (hb1 z' hz'').2
    funext u
    show NormedSpace.exp (L₁ z.2) * 1 = NormedSpace.exp (L₁ z'.2) * 1
    rw [hx] at hm
    have := congrArg (fun A => NormedSpace.exp (-L₀ z'.1) * A) hm
    simp only [← Matrix.mul_assoc, Formalism.REAL.matrix_exp_neg_mul_exp, Matrix.one_mul] at this
    rw [this]
  exact Prod.ext hx hy

end Chart

theorem placeChartV_of (hE : ExpProdU) : PlaceChartV := by
  intro n ε S hSε hgd
  set m := (subC ε S).map (rlM n) with hm
  set h := (subB ε S).map (rlM n) with hh
  let bm := stdOrthonormalBasis ℝ m
  let bh := stdOrthonormalBasis ℝ h
  let L0' : EuclideanSpace ℝ (Fin (Module.finrank ℝ m)) ≃ₗᵢ[ℝ] m := bm.repr.symm
  let L1' : EuclideanSpace ℝ (Fin (Module.finrank ℝ h)) ≃ₗᵢ[ℝ] h := bh.repr.symm
  obtain ⟨r, hr, D, hDc, hD0, hDm, hdens⟩ :=
    hE n ε m h (sup_eq_gLie ε S) (orth_CB ε S) _ _ L0' L1' hgd
  let L₀ : EuclideanSpace ℝ (Fin (Module.finrank ℝ m)) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    (urM n).comp (m.subtype.comp L0'.toLinearEquiv.toLinearMap)
  let P₀ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ m)) :=
    L0'.symm.toLinearEquiv.toLinearMap.comp ((m.orthogonalProjection : _ →L[ℝ] m).toLinearMap.comp (rlM n))
  let L₁ : EuclideanSpace ℝ (Fin (Module.finrank ℝ h)) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    (urM n).comp (h.subtype.comp L1'.toLinearEquiv.toLinearMap)
  let P₁ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ h)) :=
    L1'.symm.toLinearEquiv.toLinearMap.comp ((h.orthogonalProjection : _ →L[ℝ] h).toLinearMap.comp (rlM n))
  have hL0 : ∀ z, L₀ z = urM n (L0' z : EuclideanSpace ℝ (Fin n × Fin n × Bool)) := fun z => rfl
  have hL1 : ∀ z, L₁ z = urM n (L1' z : EuclideanSpace ℝ (Fin n × Fin n × Bool)) := fun z => rfl
  have h1 : ∀ z, P₀ (L₀ z) = z := by
    intro z
    show L0'.symm (m.orthogonalProjection (rlM n (urM n (L0' z : EuclideanSpace ℝ (Fin n × Fin n × Bool))))) = z
    rw [rl_ur, Submodule.orthogonalProjection_mem_subspace_eq_self, LinearIsometryEquiv.symm_apply_apply]
  have h2 : ∀ M, InCompl ε S M → L₀ (P₀ M) = M := by
    intro M hM
    have hmem : rlM n M ∈ m := Submodule.mem_map_of_mem (p := subC ε S) hM
    show urM n (L0' (L0'.symm (m.orthogonalProjection (rlM n M))) : EuclideanSpace ℝ (Fin n × Fin n × Bool)) = M
    rw [LinearIsometryEquiv.apply_symm_apply,
      Submodule.orthogonalProjection_mem_subspace_eq_self (⟨rlM n M, hmem⟩ : m)]
    exact ur_rl M
  have h3 : ∀ z, InCompl ε S (L₀ z) := by
    intro z
    obtain ⟨X, hX, hXe⟩ := (L0' z).2
    rw [hL0, ← hXe, ur_rl]
    exact hX
  have h4 : ∀ z, frob (L₀ z) = ‖z‖ ^ 2 := by
    intro z
    rw [hL0, frob_ur]
    exact congrArg (· ^ 2) ((Submodule.coe_norm (L0' z)).symm.trans (L0'.norm_map z))
  have h5 : ∀ z, P₁ (L₁ z) = z := by
    intro z
    show L1'.symm (h.orthogonalProjection (rlM n (urM n (L1' z : EuclideanSpace ℝ (Fin n × Fin n × Bool))))) = z
    rw [rl_ur, Submodule.orthogonalProjection_mem_subspace_eq_self, LinearIsometryEquiv.symm_apply_apply]
  have h6 : ∀ M, InBlock ε S M → L₁ (P₁ M) = M := by
    intro M hM
    have hmem : rlM n M ∈ h := Submodule.mem_map_of_mem (p := subB ε S) hM
    show urM n (L1' (L1'.symm (h.orthogonalProjection (rlM n M))) : EuclideanSpace ℝ (Fin n × Fin n × Bool)) = M
    rw [LinearIsometryEquiv.apply_symm_apply,
      Submodule.orthogonalProjection_mem_subspace_eq_self (⟨rlM n M, hmem⟩ : h)]
    exact ur_rl M
  have h7 : ∀ z, InBlock ε S (L₁ z) := by
    intro z
    obtain ⟨X, hX, hXe⟩ := (L1' z).2
    rw [hL1, ← hXe, ur_rl]
    exact hX
  have h8 : ∀ z, frob (L₁ z) = ‖z‖ ^ 2 := by
    intro z
    rw [hL1, frob_ur]
    exact congrArg (· ^ 2) ((Submodule.coe_norm (L1' z)).symm.trans (L1'.norm_map z))
  obtain ⟨rI, hrI, hinj⟩ := chart_injOn ε S L₀ L₁ h3 h4 h7 h8
  have hofr : ∀ z, ENNReal.ofReal (max (D z) 0) = ENNReal.ofReal (D z) := by
    intro z
    rcases le_total (D z) 0 with hz | hz
    · rw [max_eq_right hz, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos hz]
    · rw [max_eq_left hz]
  refine ⟨_, _, inferInstance, inferInstance, L₀, P₀, L₁, P₁, min r rI, fun z => max (D z) 0,
    h1, h2, h3, h4, h5, h6, h7, h8, lt_min hr hrI, hDc.max continuousAt_const, ?_, hDm.max measurable_const,
    fun z => le_max_right _ _, ?_, hinj.mono (ball_subset_ball (min_le_right _ _)), fun A hA hAm => ?_⟩
  · simp only
    rw [hD0]
    exact max_eq_left hgd.2.le
  · exact (continuous_expU ε (fun z : EuclideanSpace ℝ (Fin (Module.finrank ℝ m)) ×
        EuclideanSpace ℝ (Fin (Module.finrank ℝ h)) => L₀ z.1)
      (L₀.continuous_of_finiteDimensional.comp continuous_fst) fun z => (h3 z.1).1).mul
      (continuous_expU ε (fun z : EuclideanSpace ℝ (Fin (Module.finrank ℝ m)) ×
        EuclideanSpace ℝ (Fin (Module.finrank ℝ h)) => L₁ z.2)
      (L₁.continuous_of_finiteDimensional.comp continuous_snd) fun z => (h7 z.2).1)
  · have := hdens A (hA.trans (ball_subset_ball (min_le_left _ _))) hAm
    simp_rw [hofr]
    exact this

end PI.AprimeInfW
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PlaceV =====

-- ===== clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.BlockEmb =====
-- clump-header: {"m": "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.BlockEmb", "h": "module\n\npublic import Mathlib.Analysis.CStarAlgebra.Classes\npublic import Mathlib.Analysis.Normed.Algebra.Exponential\npublic import Mathlib.Topology.Instances.Matrix\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\npublic import Mathlib.Analysis.Matrix.Normed\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\nimport Mathlib.Topology.UniformSpace.Matrix\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace PI.AprimeInfG

open scoped Matrix

variable {n k : ℕ} {S : Finset (Fin n)}

def emb0 (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => if h : i ∈ S ∧ j ∈ S then X (e.symm ⟨i, h.1⟩) (e.symm ⟨j, h.2⟩) else 0

def blockEmbeddingAddHom (e : Fin k ≃ S) : Matrix (Fin k) (Fin k) ℂ →+ Matrix (Fin n) (Fin n) ℂ where
  toFun := emb0 e
  map_zero' := by
    funext i j
    simp [emb0]
  map_add' X Y := by
    funext i j
    simp only [emb0, Matrix.add_apply]
    split_ifs <;> simp

private theorem emb0_apply_coe_coe (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) (a b : Fin k) :
    emb0 e X (e a) (e b) = X a b := by
  simp [emb0]

private theorem emb0_apply_of_left_not_mem (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) {i j : Fin n}
    (hi : i ∉ S) : emb0 e X i j = 0 := by
  simp [emb0, hi]

private theorem emb0_apply_of_right_not_mem (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) {i j : Fin n}
    (hj : j ∉ S) : emb0 e X i j = 0 := by
  simp [emb0, hj]

private theorem exists_equiv_coe_eq_of_mem (e : Fin k ≃ S) {i : Fin n} (hi : i ∈ S) :
    ∃ a, (e a : Fin n) = i :=
  ⟨e.symm ⟨i, hi⟩, by simp⟩

private theorem sum_eq_sum_equiv_of_eq_zero_of_not_mem {M : Type*} [AddCommMonoid M] (e : Fin k ≃ S) (F : Fin n → M)
    (hF : ∀ l, l ∉ S → F l = 0) : ∑ l, F l = ∑ c, F (e c) := by
  rw [← Finset.sum_subset (Finset.subset_univ S) (fun l _ hl => hF l hl), ← Finset.sum_coe_sort S]
  exact (Equiv.sum_comp e (fun x : S => F x)).symm

theorem embed_mul (e : Fin k ≃ S) (X Y : Matrix (Fin k) (Fin k) ℂ) :
    emb0 e (X * Y) = emb0 e X * emb0 e Y := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ S
    · obtain ⟨a, rfl⟩ := exists_equiv_coe_eq_of_mem e hi
      obtain ⟨b, rfl⟩ := exists_equiv_coe_eq_of_mem e hj
      rw [emb0_apply_coe_coe, Matrix.mul_apply, sum_eq_sum_equiv_of_eq_zero_of_not_mem e]
      · simp only [emb0_apply_coe_coe]
      · intro l hl
        simp [emb0_apply_of_right_not_mem e X hl]
    · rw [emb0_apply_of_right_not_mem e _ hj]
      symm
      exact Finset.sum_eq_zero (fun l _ => by rw [emb0_apply_of_right_not_mem e Y hj, mul_zero])
  · rw [emb0_apply_of_left_not_mem e _ hi]
    symm
    exact Finset.sum_eq_zero (fun l _ => by rw [emb0_apply_of_left_not_mem e X hi, zero_mul])

theorem embed_pow_succ (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) (m : ℕ) :
    emb0 e (X ^ (m + 1)) = emb0 e X ^ (m + 1) := by
  induction m with
  | zero => simp only [zero_add, pow_one]
  | succ m ih => rw [pow_succ, embed_mul, ih, ← pow_succ]

private theorem emb0Add_apply (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) :
    blockEmbeddingAddHom e X = emb0 e X :=
  rfl

private theorem emb0_smul (e : Fin k ≃ S) (c : ℂ) (X : Matrix (Fin k) (Fin k) ℂ) :
    emb0 e (c • X) = c • emb0 e X := by
  ext i j
  rw [Matrix.smul_apply]
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ S
    · obtain ⟨a, rfl⟩ := exists_equiv_coe_eq_of_mem e hi
      obtain ⟨b, rfl⟩ := exists_equiv_coe_eq_of_mem e hj
      rw [emb0_apply_coe_coe, emb0_apply_coe_coe, Matrix.smul_apply]
    · rw [emb0_apply_of_right_not_mem e _ hj, emb0_apply_of_right_not_mem e _ hj, smul_zero]
  · rw [emb0_apply_of_left_not_mem e _ hi, emb0_apply_of_left_not_mem e _ hi, smul_zero]

theorem continuous_embed (e : Fin k ≃ S) : Continuous (emb0 e) := by
  refine continuous_matrix fun i j => ?_
  by_cases h : i ∈ S ∧ j ∈ S
  · simp only [emb0, dite_eq_left h]
    exact continuous_id.matrix_elem _ _
  · simp only [emb0, dite_eq_right h]
    exact continuous_const


theorem exp_embed (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) :
    NormedSpace.exp (emb0 e X) = emb0 e (NormedSpace.exp X) + (1 - emb0 e 1) := by
  letI : NormedRing (Matrix (Fin k) (Fin k) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin k) (Fin k) ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have h1 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) X
  have h2 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (emb0 e X)
  have h3 := (h1.map (blockEmbeddingAddHom e) (continuous_embed e)).add
    (hasSum_ite_eq 0 (1 - emb0 e 1))
  refine h2.unique ?_
  convert h3 using 1
  all_goals try rfl
  funext m
  rcases m with _ | m
  · simp [emb0Add_apply]
  · simp [emb0Add_apply, emb0_smul, embed_pow_succ]

def resB (e : Fin k ≃ S) (M : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  fun a b => M (e a) (e b)

theorem restrict_embed (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) : resB e (emb0 e X) = X := by
  ext a b
  exact emb0_apply_coe_coe e X a b

theorem embed_restrict (e : Fin k ≃ S) (M : Matrix (Fin n) (Fin n) ℂ) (hM : ∀ i j, (i ∉ S ∨ j ∉ S) → M i j = 0) :
    emb0 e (resB e M) = M := by
  ext i j
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ S
    · obtain ⟨a, rfl⟩ := exists_equiv_coe_eq_of_mem e hi
      obtain ⟨b, rfl⟩ := exists_equiv_coe_eq_of_mem e hj
      rw [emb0_apply_coe_coe]
      rfl
    · rw [emb0_apply_of_right_not_mem e _ hj, hM i j (Or.inr hj)]
  · rw [emb0_apply_of_left_not_mem e _ hi, hM i j (Or.inl hi)]

theorem embed_conjTranspose (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) :
    emb0 e Xᴴ = (emb0 e X)ᴴ := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ S
    · obtain ⟨a, rfl⟩ := exists_equiv_coe_eq_of_mem e hi
      obtain ⟨b, rfl⟩ := exists_equiv_coe_eq_of_mem e hj
      rw [emb0_apply_coe_coe, emb0_apply_coe_coe, Matrix.conjTranspose_apply]
    · rw [emb0_apply_of_right_not_mem e _ hj, emb0_apply_of_left_not_mem e _ hj, star_zero]
  · rw [emb0_apply_of_left_not_mem e _ hi, emb0_apply_of_right_not_mem e _ hi, star_zero]

theorem sum_norm_sq_embed (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) :
    (∑ i, ∑ j, ‖emb0 e X i j‖ ^ 2) = ∑ a, ∑ b, ‖X a b‖ ^ 2 := by
  rw [sum_eq_sum_equiv_of_eq_zero_of_not_mem e]
  · refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [sum_eq_sum_equiv_of_eq_zero_of_not_mem e]
    · simp only [emb0_apply_coe_coe]
    · intro j hj
      simp [emb0_apply_of_right_not_mem e X hj]
  · intro i hi
    simp [emb0_apply_of_left_not_mem e X hi]

end PI.AprimeInfG
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.BlockEmb =====

-- ===== clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GaugeVolU =====
-- clump-header: {"m": "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GaugeVolU", "h": "module\n\npublic import Formalism.RealPlaceAnalysis.Complexify\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace PI.AprimeInfW

theorem jm_true (k : ℕ) : Formalism.REAL.Jm (fun _ : Fin k => true) = 1 := by
  simp [Formalism.REAL.Jm]

end PI.AprimeInfW
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GaugeVolU =====

-- ===== clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.BlockEx =====
-- clump-header: {"m": "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.BlockEx", "h": "module\n\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GrpParts\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ExistsLieCompl\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct Matrix

section Block

variable {V : Type} [Fintype V] {n : ℕ}

def lieB (ε : V → Fin n → Bool) (S : V → Finset (Fin n)) : Submodule ℝ (V → Matrix (Fin n) (Fin n) ℂ) where
  carrier := {M | ∀ v, (M v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * M v = 0 ∧
    ∀ i j, (i ∉ S v ∨ j ∉ S v) → M v i j = 0}
  zero_mem' := by intro v; simp
  add_mem' := by
    intro A B hA hB v
    refine ⟨?_, fun i j hij => ?_⟩
    · have e : (A v + B v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * (A v + B v) =
          ((A v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * A v) +
            ((B v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * B v) := by
        rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]; abel
      show (A v + B v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * (A v + B v) = 0
      rw [e, (hA v).1, (hB v).1, add_zero]
    · show A v i j + B v i j = 0
      rw [(hA v).2 i j hij, (hB v).2 i j hij, add_zero]
  smul_mem' := by
    intro c A hA v
    refine ⟨?_, fun i j hij => ?_⟩
    · show (c • A v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * (c • A v) = 0
      rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, (hA v).1,
        smul_zero]
    · show c • A v i j = 0
      rw [(hA v).2 i j hij, smul_zero]

theorem exists_lieBlock (ε : V → Fin n → Bool) (S : V → Finset (Fin n)) :
    ∃ (η : Type) (_ : Fintype η) (L : EuclideanSpace ℝ η →ₗ[ℝ] (V → Matrix (Fin n) (Fin n) ℂ)),
      (∀ x v, (L x v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * L x v = 0 ∧
        ∀ i j, (i ∉ S v ∨ j ∉ S v) → L x v i j = 0) ∧
      (∀ x, ∑ v, ∑ i, ∑ j, ‖L x v i j‖ ^ 2 = ‖x‖ ^ 2) ∧
      ∀ M : V → Matrix (Fin n) (Fin n) ℂ,
        (∀ v, (M v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * M v = 0 ∧
          ∀ i j, (i ∉ S v ∨ j ∉ S v) → M v i j = 0) → ∃ x, L x = M := by
  set K' : Submodule ℝ (EuclideanSpace ℂ (V × Fin n × Fin n)) := (lieB ε S).map (entL V n).toLinearMap with hK'
  let b := stdOrthonormalBasis ℝ K'
  let L : EuclideanSpace ℝ (Fin (Module.finrank ℝ K')) →ₗ[ℝ] (V → Matrix (Fin n) (Fin n) ℂ) :=
    (entL V n).symm.toLinearMap ∘ₗ K'.subtype ∘ₗ b.repr.symm.toLinearEquiv.toLinearMap
  have hLe : ∀ x, entL V n (L x) = (b.repr.symm x : EuclideanSpace ℂ (V × Fin n × Fin n)) := by
    intro x; simp [L]
  have hLK : ∀ x, L x ∈ lieB ε S := by
    intro x
    obtain ⟨M, hM, hMe⟩ := (b.repr.symm x).2
    have : L x = M := by
      apply (entL V n).injective
      rw [hLe]; exact hMe.symm
    rw [this]; exact hM
  refine ⟨Fin (Module.finrank ℝ K'), inferInstance, L, fun x v => hLK x v, fun x => ?_, fun M hM => ?_⟩
  · rw [← norm_entL_sq, hLe]
    exact congrArg (· ^ 2) (b.repr.symm.norm_map x)
  · have hM' : entL V n M ∈ K' := ⟨M, hM, rfl⟩
    refine ⟨b.repr ⟨entL V n M, hM'⟩, ?_⟩
    apply (entL V n).injective
    rw [hLe, LinearIsometryEquiv.symm_apply_apply]

end Block

theorem blockEx_holds : BlockEx := by
  intro D X S
  obtain ⟨η, hη, L, h1, h2, h3⟩ := exists_lieBlock X.B.I.ε S
  exact ⟨η, hη, L, h1, h2, h3⟩

end PI.AprimeInfW
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.BlockEx =====

-- ===== clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GrpTop =====
-- clump-header: {"m": "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GrpTop", "h": "module\n\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GrpHaarW\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ExpProdSt\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.BlockEx\nimport Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GrpInj\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PlaceV\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.UniInf\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace PI.AprimeInfW

theorem grpDens_of_exp (hE : ExpProdU) : GrpDens :=
  grpDens_of (ginfDens_of (placeCharts_of (placeChartV_of hE))) unimodInf_holds

theorem grpStd_of_leaves (hE : ExpProdU) (hH : GrpHaarH) : GrpStd :=
  grpStd_of (grpPiecesStd_of blockEx_holds chiStab' (grpDens_of_exp hE) hH grpInj_holds)

theorem grpStd_of_exp_block (hE : ExpProdU) (hBH : BlockHaarV) : GrpStd :=
  grpStd_of_leaves hE (grpHaarH_of hBH)

end PI.AprimeInfW
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GrpTop =====

-- ===== clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.BlockGrp =====
-- clump-header: {"m": "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.BlockGrp", "h": "module\n\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.BlockEmb\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GrpHaarW\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ExpProdSt\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GaugeVolU\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GrpTop\nimport Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PlaceV\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.CategoryTheory.Countable\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Separation.CompletelyRegular\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric Set PI.AprimeInfG
open scoped Matrix

variable {n k : ℕ} {S : Finset (Fin n)}

theorem jm_mul_embed (ε : Fin n → Bool) (hε : ∀ i ∈ S, ε i = true) (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) :
    Formalism.REAL.Jm ε * emb0 e X = emb0 e X := by
  funext i j
  rw [Formalism.REAL.Jm, Matrix.diagonal_mul]
  by_cases hi : i ∈ S
  · simp [hε i hi]
  · simp [emb0, hi]

theorem embed_mul_jm (ε : Fin n → Bool) (hε : ∀ i ∈ S, ε i = true) (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) :
    emb0 e X * Formalism.REAL.Jm ε = emb0 e X := by
  funext i j
  rw [Formalism.REAL.Jm, Matrix.mul_diagonal]
  by_cases hj : j ∈ S
  · simp [hε j hj]
  · simp [emb0, hj]

theorem embed_mul_complement (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) : emb0 e X * (1 - emb0 e 1) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, ← embed_mul, Matrix.mul_one, sub_self]

theorem complement_mul_embed (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) : (1 - emb0 e 1) * emb0 e X = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, ← embed_mul, Matrix.one_mul, sub_self]

theorem P_mul_P (e : Fin k ≃ S) : (1 - emb0 e 1) * (1 - emb0 e 1 : Matrix (Fin n) (Fin n) ℂ) = 1 - emb0 e 1 := by
  rw [Matrix.mul_sub, Matrix.mul_one, complement_mul_embed, sub_zero]

def blkM (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) : Matrix (Fin n) (Fin n) ℂ := emb0 e X + (1 - emb0 e 1)

theorem blkM_mul (e : Fin k ≃ S) (X Y : Matrix (Fin k) (Fin k) ℂ) : blkM e X * blkM e Y = blkM e (X * Y) := by
  unfold blkM
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, embed_mul_complement, complement_mul_embed, P_mul_P, ← embed_mul]
  abel

theorem blkM_one (e : Fin k ≃ S) : blkM e (1 : Matrix (Fin k) (Fin k) ℂ) = 1 := by
  unfold blkM; abel

theorem blkM_conjTranspose_mul_jm_mul_blkM (ε : Fin n → Bool) (hε : ∀ i ∈ S, ε i = true) (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) :
    (blkM e X)ᴴ * Formalism.REAL.Jm ε * blkM e X = emb0 e (Xᴴ * X) + Formalism.REAL.Jm ε * (1 - emb0 e 1) := by
  have hPh : (1 - emb0 e 1 : Matrix (Fin n) (Fin n) ℂ)ᴴ = 1 - emb0 e 1 := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, ← embed_conjTranspose, Matrix.conjTranspose_one]
  have hJP : Formalism.REAL.Jm ε * (1 - emb0 e 1) = (1 - emb0 e 1) * Formalism.REAL.Jm ε := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, jm_mul_embed ε hε, embed_mul_jm ε hε]
  unfold blkM
  rw [Matrix.conjTranspose_add, hPh, ← embed_conjTranspose]
  have e1 : (emb0 e Xᴴ + (1 - emb0 e 1)) * Formalism.REAL.Jm ε * (emb0 e X + (1 - emb0 e 1)) =
      emb0 e Xᴴ * Formalism.REAL.Jm ε * emb0 e X + emb0 e Xᴴ * (Formalism.REAL.Jm ε * (1 - emb0 e 1)) +
        (1 - emb0 e 1) * Formalism.REAL.Jm ε * emb0 e X + (1 - emb0 e 1) * (Formalism.REAL.Jm ε * (1 - emb0 e 1)) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
    abel
  rw [e1, embed_mul_jm ε hε, hJP, ← Matrix.mul_assoc (emb0 e Xᴴ), embed_mul_complement, Matrix.zero_mul,
    Matrix.mul_assoc (1 - emb0 e 1), jm_mul_embed ε hε, complement_mul_embed, ← Matrix.mul_assoc, P_mul_P, ← embed_mul, ← hJP]
  abel

theorem blkM_col (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) (i : Fin n) (hi : i ∉ S) (j : Fin n) :
    blkM e X j i = if j = i then 1 else 0 := by
  simp [blkM, emb0, hi, Matrix.one_apply]

theorem blkM_inj (e : Fin k ≃ S) {X Y : Matrix (Fin k) (Fin k) ℂ} (h : blkM e X = blkM e Y) : X = Y := by
  unfold blkM at h
  have := congrArg (resB e) (add_right_cancel h)
  rwa [restrict_embed, restrict_embed] at this

theorem inUJ_blkM (ε : Fin n → Bool) (hε : ∀ i ∈ S, ε i = true) (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ)
    (hX : Xᴴ * X = 1) : Formalism.REAL.inUJ ε (blkM e X) := by
  unfold Formalism.REAL.inUJ
  rw [blkM_conjTranspose_mul_jm_mul_blkM ε hε, hX, Matrix.mul_sub, Matrix.mul_one, jm_mul_embed ε hε]
  abel

def embHom (ε : Fin n → Bool) (hε : ∀ i ∈ S, ε i = true) (e : Fin k ≃ S) :
    Formalism.REAL.UJ (fun _ : Fin k => true) →* UstdSub ε S where
  toFun g :=
    ⟨⟨⟨blkM e ((g : (Matrix (Fin k) (Fin k) ℂ)ˣ) : Matrix (Fin k) (Fin k) ℂ),
        blkM e (((g : (Matrix (Fin k) (Fin k) ℂ)ˣ)⁻¹ : (Matrix (Fin k) (Fin k) ℂ)ˣ) : Matrix (Fin k) (Fin k) ℂ),
        by rw [blkM_mul, Units.mul_inv, blkM_one], by rw [blkM_mul, Units.inv_mul, blkM_one]⟩,
      inUJ_blkM ε hε e _ (by
        have h := g.2
        change ((g : (Matrix (Fin k) (Fin k) ℂ)ˣ) : Matrix (Fin k) (Fin k) ℂ)ᴴ * Formalism.REAL.Jm (fun _ : Fin k => true) *
          ((g : (Matrix (Fin k) (Fin k) ℂ)ˣ) : Matrix (Fin k) (Fin k) ℂ) = Formalism.REAL.Jm (fun _ : Fin k => true) at h
        rwa [jm_true, Matrix.mul_one] at h)⟩,
      fun i hi j => blkM_col e _ i hi j⟩
  map_one' := by
    apply Subtype.ext; apply Subtype.ext; apply Units.ext
    exact blkM_one e
  map_mul' g h := by
    apply Subtype.ext; apply Subtype.ext; apply Units.ext
    exact (blkM_mul e _ _).symm

theorem embHom_val (ε : Fin n → Bool) (hε : ∀ i ∈ S, ε i = true) (e : Fin k ≃ S)
    (g : Formalism.REAL.UJ (fun _ : Fin k => true)) :
    ((((embHom ε hε e g : UstdSub ε S) : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) =
      blkM e ((g : (Matrix (Fin k) (Fin k) ℂ)ˣ) : Matrix (Fin k) (Fin k) ℂ) := rfl

theorem embHom_injective (ε : Fin n → Bool) (hε : ∀ i ∈ S, ε i = true) (e : Fin k ≃ S) :
    Function.Injective (embHom ε hε e) := by
  intro g h he
  have := congrArg (fun u : UstdSub ε S => (((u : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
    Matrix (Fin n) (Fin n) ℂ)) he
  simp only [embHom_val] at this
  exact Subtype.ext (Units.ext (blkM_inj e this))

theorem std_row (ε : Fin n → Bool) (u : UstdSub ε S) (i : Fin n) (hi : i ∉ S) (j : Fin n) (hji : j ≠ i) :
    (((u : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) i j = 0 := by
  set U := (((u : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) with hU
  set V := ((((u : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ))⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) with hV
  have hUV : U * (V : Matrix (Fin n) (Fin n) ℂ) = 1 := Units.mul_inv _
  have hJ : Uᴴ * Formalism.REAL.Jm ε * U = Formalism.REAL.Jm ε := (u : Formalism.REAL.UJ ε).2
  have hJJ := Formalism.REAL.Jm_mul_self ε
  have hW : Formalism.REAL.Jm ε * Uᴴ * Formalism.REAL.Jm ε = (V : Matrix (Fin n) (Fin n) ℂ) := by
    calc Formalism.REAL.Jm ε * Uᴴ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * Uᴴ * Formalism.REAL.Jm ε * (U * V) := by
          rw [hUV, Matrix.mul_one]
      _ = Formalism.REAL.Jm ε * (Uᴴ * Formalism.REAL.Jm ε * U) * V := by simp only [Matrix.mul_assoc]
      _ = (V : Matrix (Fin n) (Fin n) ℂ) := by rw [hJ, hJJ, Matrix.one_mul]
  have hcol := (u⁻¹).2 i hi j
  change (V : Matrix (Fin n) (Fin n) ℂ) j i = _ at hcol
  rw [← hW, ite_eq_right hji] at hcol
  simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply] at hcol
  have hd : ∀ a : Fin n, (if ε a = true then (1 : ℂ) else -1) ≠ 0 := fun a => by split_ifs <;> norm_num
  have := (mul_eq_zero.1 hcol).resolve_right (hd i)
  have := (mul_eq_zero.1 this).resolve_left (hd j)
  simpa using this

theorem std_eq_blkM (ε : Fin n → Bool) (e : Fin k ≃ S) (u : UstdSub ε S) :
    (((u : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) =
      blkM e (resB e (((u : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) := by
  funext a b
  by_cases hb : b ∈ S
  · by_cases ha : a ∈ S
    · simp [blkM, emb0, resB, ha, hb, Matrix.one_apply]
    · have hab : b ≠ a := fun h => ha (h ▸ hb)
      rw [std_row ε u a ha b hab]
      simp [blkM, emb0, ha, hab.symm]
  · rw [u.2 b hb a, blkM_col e _ b hb a]

theorem embHom_surjective (ε : Fin n → Bool) (hε : ∀ i ∈ S, ε i = true) (e : Fin k ≃ S) :
    Function.Surjective (embHom ε hε e) := by
  intro u
  set U := (((u : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) with hU
  set V := ((((u⁻¹ : UstdSub ε S) : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) with hV
  have hUb := std_eq_blkM ε e u
  have hVb := std_eq_blkM ε e u⁻¹
  have hUV : U * V = 1 := Units.mul_inv _
  have hVU : V * U = 1 := Units.inv_mul _
  have h1 : resB e U * resB e V = 1 := by
    apply blkM_inj e
    rw [← blkM_mul, ← hUb, ← hVb, hUV, blkM_one]
  have h2 : resB e V * resB e U = 1 := by
    apply blkM_inj e
    rw [← blkM_mul, ← hUb, ← hVb, hVU, blkM_one]
  have hJ : Uᴴ * Formalism.REAL.Jm ε * U = Formalism.REAL.Jm ε := (u : Formalism.REAL.UJ ε).2
  have hGG : (resB e U)ᴴ * resB e U = 1 := by
    have h3 := blkM_conjTranspose_mul_jm_mul_blkM ε hε e (resB e U)
    rw [← hUb, hJ] at h3
    have h4 : Formalism.REAL.Jm ε = emb0 e 1 + Formalism.REAL.Jm ε * (1 - emb0 e 1) := by
      rw [Matrix.mul_sub, Matrix.mul_one, jm_mul_embed ε hε]; abel
    have h5 := add_right_cancel (h4.symm.trans h3)
    have := congrArg (resB e) h5
    rw [restrict_embed, restrict_embed] at this
    exact this.symm
  refine ⟨⟨⟨resB e U, resB e V, h1, h2⟩, ?_⟩, ?_⟩
  · change (resB e U)ᴴ * Formalism.REAL.Jm (fun _ : Fin k => true) * resB e U = Formalism.REAL.Jm (fun _ : Fin k => true)
    rw [jm_true, Matrix.mul_one, hGG]
  · apply Subtype.ext; apply Subtype.ext; apply Units.ext
    rw [embHom_val]
    exact hUb.symm

def blockEmbeddingLinearMap (e : Fin k ≃ S) : Matrix (Fin k) (Fin k) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := emb0 e
  map_add' := (blockEmbeddingAddHom e).map_add
  map_smul' c X := by
    funext i j
    simp only [emb0, Matrix.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

def resBLin (e : Fin k ≃ S) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin k) (Fin k) ℂ where
  toFun := resB e
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def UkChart : Prop := ∀ k : ℕ, Formalism.MainNotions.S.Gauge.GaugeDens (fun _ : Fin k => true) →
    ∃ (α : Type) (_ : Fintype α) (L₀ : EuclideanSpace ℝ α →ₗ[ℝ] Matrix (Fin k) (Fin k) ℂ)
      (P₀ : Matrix (Fin k) (Fin k) ℂ →ₗ[ℝ] EuclideanSpace ℝ α) (r : ℝ) (D : EuclideanSpace ℝ α → ℝ),
      (∀ z, P₀ (L₀ z) = z) ∧
      (∀ M, Mᴴ * Formalism.REAL.Jm (fun _ : Fin k => true) + Formalism.REAL.Jm (fun _ : Fin k => true) * M = 0 → L₀ (P₀ M) = M) ∧
      (∀ z, (L₀ z)ᴴ * Formalism.REAL.Jm (fun _ : Fin k => true) + Formalism.REAL.Jm (fun _ : Fin k => true) * L₀ z = 0) ∧
      (∀ z, frob (L₀ z) = ‖z‖ ^ 2) ∧ 0 < r ∧ ContinuousAt D 0 ∧
      D 0 = Formalism.MainNotions.S.Gauge.gaugeU (fun _ : Fin k => true) ∧ Measurable D ∧ (∀ z, 0 ≤ D z) ∧
      Set.InjOn (fun z => expU (fun _ : Fin k => true) (L₀ z)) (ball 0 r) ∧
      ∀ A ⊆ ball (0 : EuclideanSpace ℝ α) r, MeasurableSet A →
        Formalism.REAL.muG (fun _ : Fin k => true) ((fun z => expU (fun _ : Fin k => true) (L₀ z)) '' A) =
          ∫⁻ z in A, ENNReal.ofReal (D z)

def GaugeVolUD : Prop := ∀ k : ℕ, Formalism.MainNotions.S.Gauge.GaugeDens (fun _ : Fin k => true) ∧
    Formalism.MainNotions.S.Gauge.muGauge (fun _ : Fin k => true) Set.univ = ENNReal.ofReal (Formalism.MainNotions.S.UnitaryVolumeMass.volU k)

theorem continuous_embHom (ε : Fin n → Bool) (hε : ∀ i ∈ S, ε i = true) (e : Fin k ≃ S) :
    Continuous (embHom ε hε e) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  rw [Units.continuous_iff]
  constructor
  · exact ((continuous_embed e).comp (Units.continuous_val.comp continuous_subtype_val)).add continuous_const
  · exact ((continuous_embed e).comp (Units.continuous_coe_inv.comp continuous_subtype_val)).add continuous_const

theorem blockHaarV_of (hU : UkChart) (hG : GaugeVolUD) : BlockHaarV := by
  intro n ε S k hk hε _
  let e : Fin k ≃ S := (finCongr hk.symm).trans S.equivFin.symm
  obtain ⟨α, hα, L0, P0, r, D, f1, f2, f3, f4, hr, hDc, hD0, hDm, hDn, hinj, hdens⟩ := hU k (hG k).1
  have hJk := jm_true k

  let L₁ : EuclideanSpace ℝ α →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ := (blockEmbeddingLinearMap e).comp L0
  let P₁ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] EuclideanSpace ℝ α := P0.comp (resBLin e)
  have hL₁ : ∀ y, L₁ y = emb0 e (L0 y) := fun y => rfl
  have hblk : ∀ y, InBlock ε S (L₁ y) := by
    intro y
    refine ⟨?_, fun i j hij => ?_⟩
    · rw [hL₁, ← embed_conjTranspose, embed_mul_jm ε hε, jm_mul_embed ε hε]
      have h := f3 y
      rw [hJk, Matrix.mul_one, Matrix.one_mul] at h
      have := congrArg (emb0 e) h
      rw [show emb0 e (0 : Matrix (Fin k) (Fin k) ℂ) = 0 from (blockEmbeddingAddHom e).map_zero] at this
      rw [← this]
      exact ((blockEmbeddingAddHom e).map_add _ _).symm
    · rw [hL₁]
      rcases hij with hi | hj
      · simp [emb0, hi]
      · simp [emb0, hj]
  have hmem : ∀ y, expU ε (L₁ y) ∈ UstdSub ε S := by
    intro y i hi j
    show ((expU ε (L₁ y) : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) j i = _
    rw [expU_val _ _ (hblk y).1]
    exact exp_block_col S _ (hblk y).2 i hi j

  have hchart : ∀ y, embHom ε hε e (expU (fun _ : Fin k => true) (L0 y)) = ⟨expU ε (L₁ y), hmem y⟩ := by
    intro y
    apply Subtype.ext; apply Subtype.ext; apply Units.ext
    rw [embHom_val]
    show blkM e (((expU (fun _ : Fin k => true) (L0 y) : Formalism.REAL.UJ _) : (Matrix (Fin k) (Fin k) ℂ)ˣ) :
      Matrix (Fin k) (Fin k) ℂ) = ((expU ε (L₁ y) : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    rw [expU_val _ _ (f3 y), expU_val _ _ (hblk y).1, hL₁, exp_embed]
    rfl

  have hgpos : 0 < Formalism.MainNotions.S.Gauge.gaugeU (fun _ : Fin k => true) := (hG k).1.2
  have hvol := (hG k).2
  unfold Formalism.MainNotions.S.Gauge.muGauge at hvol
  rw [Measure.smul_apply, smul_eq_mul] at hvol
  have hfin : Formalism.REAL.muG (fun _ : Fin k => true) Set.univ ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.mul_top (by simp [hgpos])] at hvol
    exact ENNReal.ofReal_ne_top hvol.symm
  have hpos : Formalism.REAL.muG (fun _ : Fin k => true) Set.univ ≠ 0 :=
    (Measure.measure_univ_pos.2 (NeZero.ne _)).ne'
  have : IsFiniteMeasure (Formalism.REAL.muG (fun _ : Fin k => true)) := ⟨lt_top_iff_ne_top.2 hfin⟩
  have hcE := continuous_embHom ε hε e
  let ν := (Formalism.REAL.muG (fun _ : Fin k => true)).map (embHom ε hε e)
  have hνu : ν Set.univ = Formalism.REAL.muG (fun _ : Fin k => true) Set.univ := by
    rw [Measure.map_apply hcE.measurable MeasurableSet.univ, Set.preimage_univ]
  refine ⟨α, hα, L₁, P₁, ν, r, D, hmem, fun z => ?_, fun M hM => ?_, hblk, fun z => ?_,
    isMulLeftInvariant_map (embHom ε hε e).toMulHom hcE.measurable (embHom_surjective ε hε e), inferInstance,
    ?_, hr, hDm, hDn, hDc, ?_, ?_, ?_, ?_, fun A hA hAm => ?_⟩
  · show P0 (resB e (emb0 e (L0 z))) = z
    rw [restrict_embed, f1]
  · show emb0 e (L0 (P0 (resB e M))) = M
    have hl : (resB e M)ᴴ * Formalism.REAL.Jm (fun _ : Fin k => true) + Formalism.REAL.Jm (fun _ : Fin k => true) * resB e M = 0 := by
      rw [hJk, Matrix.mul_one, Matrix.one_mul]
      funext a b
      have h := congrFun (congrFun hM.1 (e a)) (e b)
      rw [PI.AprimeInfW.lie_entry] at h
      have ha : ((e a : S) : Fin n) ∈ S := (e a).2
      have hb : ((e b : S) : Fin n) ∈ S := (e b).2
      simp only [hε _ ha, hε _ hb, ite_true, mul_one, one_mul] at h
      simpa [resB, Matrix.conjTranspose_apply] using h
    rw [f2 _ hl, embed_restrict e M hM.2]
  · rw [hL₁]
    unfold frob
    rw [sum_norm_sq_embed]
    exact f4 z
  · rw [hνu]; exact hpos
  · rw [hD0]; exact hgpos
  · rw [hνu, hD0]
    have := congrArg ENNReal.toReal hvol
    have hv0 : 0 ≤ Formalism.MainNotions.S.UnitaryVolumeMass.volU k := by
      unfold Formalism.MainNotions.S.UnitaryVolumeMass.volU; exact Finset.prod_nonneg fun i _ => by positivity
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.2 hgpos.le), ENNReal.toReal_ofReal hv0] at this
    rw [← this]
    field_simp
  · exact (continuous_expU ε (fun y => L₁ y) L₁.continuous_of_finiteDimensional fun y => (hblk y).1).subtype_mk _
  · intro y hy y' hy' he'
    apply hinj hy hy'
    apply embHom_injective ε hε e
    rw [hchart, hchart]
    exact he'
  · have himg : (fun y => (⟨expU ε (L₁ y), hmem y⟩ : UstdSub ε S)) '' A =
        embHom ε hε e '' ((fun z => expU (fun _ : Fin k => true) (L0 z)) '' A) := by
      rw [Set.image_image]
      exact Set.image_congr fun y _ => (hchart y).symm
    have hcont : Continuous (fun y => (⟨expU ε (L₁ y), hmem y⟩ : UstdSub ε S)) :=
      (continuous_expU ε (fun y => L₁ y) L₁.continuous_of_finiteDimensional fun y => (hblk y).1).subtype_mk _
    have hinj' : Set.InjOn (fun y => (⟨expU ε (L₁ y), hmem y⟩ : UstdSub ε S)) A := by
      intro y hy y' hy' he'
      apply hinj (hA hy) (hA hy')
      apply embHom_injective ε hε e
      rw [hchart, hchart]
      exact he'
    have hmeas : MeasurableSet ((fun y => (⟨expU ε (L₁ y), hmem y⟩ : UstdSub ε S)) '' A) :=
      hAm.image_of_continuousOn_injOn hcont.continuousOn hinj'
    rw [Measure.map_apply hcE.measurable hmeas, himg, (embHom_injective ε hε e).preimage_image]
    exact hdens A hA hAm

theorem ukChart_of (hE : ExpProdU) : UkChart := by
  intro k hgd
  obtain ⟨α, β, hα, hβ, L0, P0, L1, P1, r, D, f1, f2, f3, f4, f5, f6, f7, f8, hr, hDc, hD0, hDm, hDn, hc, hinj,
    hdens⟩ := placeChartV_of hE k (fun _ => true) ∅ (fun i hi => absurd hi (Finset.notMem_empty i)) hgd
  have hL1 : ∀ z, L1 z = 0 := by
    intro z
    funext i j
    exact (f7 z).2 i j (Or.inl (Finset.notMem_empty i))
  have hsub : ∀ z : EuclideanSpace ℝ β, z = 0 := by
    intro z
    rw [← f5 z, hL1, map_zero]
  have hβe : IsEmpty β := ⟨fun b => by
    classical
    have := congrFun (congrArg WithLp.ofLp (hsub (EuclideanSpace.single b 1))) b
    simp at this⟩
  have hvolβ : (volume : Measure (EuclideanSpace ℝ β)) Set.univ = 1 := by
    have hmp := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp β).measure_preimage
      (s := Set.univ) MeasurableSet.univ.nullMeasurableSet
    rw [Set.preimage_univ] at hmp
    rw [hmp, MeasureTheory.volume_pi, Measure.pi_univ]
    simp
  refine ⟨α, hα, L0, P0, r, fun y => D (y, 0), f1, fun M hM => f2 M ⟨hM, fun i hi => absurd hi (Finset.notMem_empty i)⟩,
    fun z => (f3 z).1, f4, hr, ?_, hD0, hDm.comp (measurable_id.prodMk measurable_const), fun z => hDn _, ?_, ?_⟩
  · exact ContinuousAt.comp (f := fun y : EuclideanSpace ℝ α => (y, (0 : EuclideanSpace ℝ β))) hDc
      (continuous_id.prodMk continuous_const).continuousAt
  · intro y hy y' hy' he
    have h1 : ((y, (0 : EuclideanSpace ℝ β)) : EuclideanSpace ℝ α × EuclideanSpace ℝ β) ∈ ball 0 r := by
      rw [mem_ball_zero_iff, Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]
      exact mem_ball_zero_iff.1 hy
    have h2 : ((y', (0 : EuclideanSpace ℝ β)) : EuclideanSpace ℝ α × EuclideanSpace ℝ β) ∈ ball 0 r := by
      rw [mem_ball_zero_iff, Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]
      exact mem_ball_zero_iff.1 hy'
    have := hinj h1 h2 (by simp only [hL1, expU_zero, mul_one]; exact he)
    exact congrArg Prod.fst this
  · intro A hA hAm
    have hAU : A ×ˢ (Set.univ : Set (EuclideanSpace ℝ β)) ⊆ ball 0 r := by
      rintro ⟨x, z⟩ ⟨hx, -⟩
      rw [hsub z, mem_ball_zero_iff, Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]
      exact mem_ball_zero_iff.1 (hA hx)
    have himg : (fun z : EuclideanSpace ℝ α × EuclideanSpace ℝ β =>
        expU (fun _ : Fin k => true) (L0 z.1) * expU (fun _ : Fin k => true) (L1 z.2)) '' (A ×ˢ Set.univ) =
        (fun z => expU (fun _ : Fin k => true) (L0 z)) '' A := by
      ext g
      constructor
      · rintro ⟨⟨x, z⟩, ⟨hx, -⟩, rfl⟩
        exact ⟨x, hx, by simp [hL1, expU_zero]⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨(x, 0), ⟨hx, Set.mem_univ _⟩, by simp [hL1, expU_zero]⟩
    rw [← himg, hdens _ hAU (hAm.prod MeasurableSet.univ), Measure.volume_eq_prod,
      setLIntegral_prod _ ((hDm.ennreal_ofReal).aemeasurable)]
    refine setLIntegral_congr_fun hAm fun x _ => ?_
    rw [show (fun z : EuclideanSpace ℝ β => ENNReal.ofReal (D (x, z))) = fun _ => ENNReal.ofReal (D (x, 0)) from
      funext fun z => by rw [hsub z], setLIntegral_const, hvolβ, mul_one]

theorem grpStd_full (hE : ExpProdU) (hG : GaugeVolUD) : GrpStd :=
  grpStd_of_exp_block hE (blockHaarV_of (ukChart_of hE) hG)

end PI.AprimeInfW
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.BlockGrp =====
