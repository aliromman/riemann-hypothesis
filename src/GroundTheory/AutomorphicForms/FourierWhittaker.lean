module

public import GroundTheory.AutomorphicForms.FourierWhittaker.Smooth
public import GroundTheory.AutomorphicForms.FourierWhittaker.AdelicCharPairTorusPtSingle
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.ConstantTerm
public import GroundTheory.AutomorphicForms.FourierWhittaker.PartialCoeffDiagonalBlockGLEqVecCoeff
public import GroundTheory.AutomorphicForms.FourierWhittaker.IsAddFundamentalDomainImageOfMapVecLattice
public import GroundTheory.AutomorphicForms.FourierWhittaker.Series
public import GroundTheory.AutomorphicForms.FourierWhittaker.AlgebraMapIntegerMemIntegralFiniteAdeles
public import GroundTheory.AutomorphicForms.FourierWhittaker.UMatColXEqFromBlocks
import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.TypeStar
import GroundTheory.AutomorphicForms.ReductionMeasure
import Mathlib.CategoryTheory.Countable
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Uniform
import GroundTheory.GlobalFields.Adele.Topology

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: GroundTheory.AutomorphicForms.FourierWhittaker.Single, GroundTheory.AutomorphicForms.FourierWhittaker.PartialCoeffBlockGLEqOfVecMulEq, GroundTheory.AutomorphicForms.FourierWhittaker.IsAddFundamentalDomainShearSymm, GroundTheory.AutomorphicForms.FourierWhittaker

-- ===== clump member: GroundTheory.AutomorphicForms.FourierWhittaker.Single =====
-- clump-header: {"m": "GroundTheory.AutomorphicForms.FourierWhittaker.Single", "h": "module\n\npublic import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.ConstantTerm\npublic import GroundTheory.AutomorphicForms.FourierWhittaker.PartialCoeffDiagonalBlockGLEqVecCoeff\nimport GroundTheory.AutomorphicForms.ReductionMeasure\nimport GroundTheory.GlobalFields.Adele.Topology\nimport Mathlib.Tactic.TypeStar\n\n"}
section -- clump:auto
@[expose] public section

open NumberField NumberField.mixedEmbedding MeasureTheory Topology Set Filter IsDedekindDomain Matrix
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace FourierWhittaker

open AutomorphicForm

variable {K : Type*} [Field K] [NumberField K]

theorem setIntegral_vecDomain_sum {ι ι₁ ι₂ : Type*} [Fintype ι] [Fintype ι₁] [Fintype ι₂]
    (e : ι ≃ ι₁ ⊕ ι₂) {h : (ι → 𝔸[K]) → ℂ} (hc : Continuous h) :
    ∫ z in vecDomain K ι, h z ∂vecMeasure K ι =
      ∫ x in vecDomain K ι₁, ∫ y in vecDomain K ι₂, h (fun i => Sum.elim x y (e i))
        ∂vecMeasure K ι₂ ∂vecMeasure K ι₁ := by
  let E : (ι → 𝔸[K]) ≃ᵐ (ι₁ → 𝔸[K]) × (ι₂ → 𝔸[K]) :=
    (MeasurableEquiv.piCongrLeft (fun _ : ι₁ ⊕ ι₂ => 𝔸[K]) e).trans
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : ι₁ ⊕ ι₂ => 𝔸[K]))
  have hE : MeasurePreserving E (vecMeasure K ι) ((vecMeasure K ι₁).prod (vecMeasure K ι₂)) :=
    (measurePreserving_piCongrLeft (fun _ : ι₁ ⊕ ι₂ => GroundTheory.Global.adeleMeasure K) e).trans
      (measurePreserving_sumPiEquivProdPi (fun _ : ι₁ ⊕ ι₂ => GroundTheory.Global.adeleMeasure K))
  have hEsymm : ∀ p, E.symm p = fun i => Sum.elim p.1 p.2 (e i) := by
    intro p
    funext i
    simp [E, MeasurableEquiv.piCongrLeft, MeasurableEquiv.sumPiEquivProdPi, Equiv.piCongrLeft,
      Equiv.sumPiEquivProdPi]
    generalize e i = j
    cases j <;> rfl
  have hpre : E ⁻¹' (vecDomain K ι₁ ×ˢ vecDomain K ι₂) = vecDomain K ι := by
    ext z
    simp only [Set.mem_preimage, Set.mem_prod, vecDomain, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · rintro ⟨h1, h2⟩ i
      have hz : z = E.symm (E z) := (E.symm_apply_apply z).symm
      rw [hz, hEsymm]
      show ((E z).1 ⊕ᵥ (E z).2) (e i) ∈ _
      rcases e i with a | b
      · exact h1 a
      · exact h2 b
    · intro h
      refine ⟨fun a => ?_, fun b => ?_⟩
      · have := h (e.symm (Sum.inl a)); simpa [E, MeasurableEquiv.piCongrLeft,
          MeasurableEquiv.sumPiEquivProdPi, Equiv.piCongrLeft, Equiv.sumPiEquivProdPi] using this
      · have := h (e.symm (Sum.inr b)); simpa [E, MeasurableEquiv.piCongrLeft,
          MeasurableEquiv.sumPiEquivProdPi, Equiv.piCongrLeft, Equiv.sumPiEquivProdPi] using this
  rw [← hpre]
  have h1 := hE.setIntegral_preimage_emb E.measurableEmbedding (fun p => h (E.symm p))
    (vecDomain K ι₁ ×ˢ vecDomain K ι₂)
  simp only [E.symm_apply_apply] at h1
  rw [h1, setIntegral_prod]
  · simp only [hEsymm]
  · have hcont : Continuous fun p : (ι₁ → 𝔸[K]) × (ι₂ → 𝔸[K]) => h (E.symm p) := by
      simp_rw [hEsymm]
      refine hc.comp (continuous_pi fun i => ?_)
      rcases e i with a | b
      · exact (continuous_apply a).comp continuous_fst
      · exact (continuous_apply b).comp continuous_snd
    exact (hcont.continuousOn.integrableOn_compact ((isCompact_closure_vecDomain (K := K)
      (ι := ι₁)).prod (isCompact_closure_vecDomain (K := K) (ι := ι₂)))).mono_set
      (Set.prod_mono subset_closure subset_closure)

variable {n : ℕ}

abbrev GePos (n k : ℕ) : Type := {p : Pos n // k ≤ p.1.2.val}

def extGe {R : Type*} [Zero R] {k : ℕ} (Z : GePos n k → R) : Pos n → R :=
  fun p => if h : k ≤ p.1.2.val then Z ⟨p, h⟩ else 0

def supSum (m : ℕ) (X : Pos n → 𝔸[K]) : 𝔸[K] :=
  ∑ p ∈ Finset.univ.filter (fun p : Pos n => p.1.2.val = p.1.1.val + 1 ∧ m ≤ p.1.2.val), X p

theorem supSum_add (m : ℕ) (X Y : Pos n → 𝔸[K]) : supSum m (X + Y) = supSum m X + supSum m Y := by
  simp [supSum, Finset.sum_add_distrib]

theorem supSum_zero (m : ℕ) : supSum m (0 : Pos n → 𝔸[K]) = 0 := by simp [supSum]

theorem supSum_colX_succ (k : ℕ) (x : Fin k → 𝔸[K]) : supSum (k + 1) (colX (n := n) k x) = 0 := by
  refine Finset.sum_eq_zero fun p hp => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
  rw [colX_apply, dite_eq_right (by omega)]

theorem supSum_colX (k : ℕ) (hk : k < n) (x : Fin k → 𝔸[K]) :
    supSum k (colX (n := n) k x) = pair (lastVec k) x := by
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [supSum]
    simp only [pair, Finset.univ_eq_empty, Finset.sum_empty]
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [colX_apply, dite_eq_right]
    have := p.2
    rw [Fin.lt_def] at this
    omega
  · have hmem : ∀ p : Pos n, (p.1.2.val = p.1.1.val + 1 ∧ k ≤ p.1.2.val) → p.1.2.val = k →
        p = ⟨(⟨k - 1, by omega⟩, ⟨k, hk⟩), by rw [Fin.lt_def]; simp; omega⟩ := by
      intro p h1 h2
      apply Subtype.ext
      apply Prod.ext <;> apply Fin.ext <;> simp <;> omega
    rw [supSum, Finset.sum_eq_single ⟨(⟨k - 1, by omega⟩, ⟨k, hk⟩), by rw [Fin.lt_def]; simp; omega⟩]
    · rw [colX_apply, dite_eq_left rfl, pair, Finset.sum_eq_single ⟨k - 1, by omega⟩]
      · simp [lastVec]; congr 1; omega
      · intro i _ hi
        rw [lastVec, ite_eq_right (fun h => hi (Fin.ext (by show i.val = k - 1; omega))), map_zero, zero_mul]
      · simp
    · intro p hp hne
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      rw [colX_apply, dite_eq_right (fun h => hne (hmem p hp h))]
    · intro h
      exfalso
      apply h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor <;> (try simp) <;> omega

theorem extGe_eq_zero {R : Type*} [Zero R] {k : ℕ} (Z : GePos n (k + 1) → R) (p : Pos n)
    (hp : p.1.2.val ≤ k) : extGe Z p = 0 := by
  rw [extGe, dite_eq_right (by omega)]

def colSplit (k : ℕ) (hk : k < n) : GePos n k ≃ Fin k ⊕ GePos n (k + 1) where
  toFun p := if h : p.1.1.2.val = k then
      Sum.inl ⟨p.1.1.1.val, by have := p.1.2; rw [Fin.lt_def] at this; omega⟩
    else Sum.inr ⟨p.1, by have := p.2; omega⟩
  invFun := Sum.elim (fun a => ⟨⟨(⟨a.val, by omega⟩, ⟨k, hk⟩), by rw [Fin.lt_def]; exact a.2⟩,
    le_refl k⟩) (fun q => ⟨q.1, by have := q.2; omega⟩)
  left_inv p := by
    by_cases h : p.1.1.2.val = k
    · simp only [dite_eq_left h, Sum.elim_inl]
      apply Subtype.ext; apply Subtype.ext
      apply Prod.ext <;> apply Fin.ext <;> simp [h]
    · simp only [dite_eq_right h, Sum.elim_inr]
  right_inv q := by
    rcases q with a | q
    · simp
    · have := q.2
      show (if h : q.1.1.2.val = k then _ else _) = _
      rw [dite_eq_right (show ¬ q.1.1.2.val = k by omega)]
      rfl

theorem extGe_colSplit {R : Type*} [CommRing R] (k : ℕ) (hk : k < n) (x : Fin k → R)
    (y : GePos n (k + 1) → R) :
    extGe (fun i => Sum.elim x y (colSplit k hk i)) = extGe y + colX k x := by
  funext p
  simp only [extGe, colX_apply, Pi.add_apply]
  by_cases h1 : k ≤ p.1.2.val
  · rw [dite_eq_left h1]
    by_cases h2 : p.1.2.val = k
    · rw [dite_eq_right (by omega), dite_eq_left h2, zero_add]
      show Sum.elim x y (colSplit k hk ⟨p, h1⟩) = _
      simp only [colSplit, Equiv.coe_fn_mk, dite_eq_left h2, Sum.elim_inl]
    · rw [dite_eq_left (by omega), dite_eq_right h2, add_zero]
      show Sum.elim x y (colSplit k hk ⟨p, h1⟩) = _
      simp only [colSplit, Equiv.coe_fn_mk, dite_eq_right h2, Sum.elim_inr]
  · rw [dite_eq_right h1, dite_eq_right (by omega), dite_eq_right (by omega), add_zero]

theorem continuous_extGe {k : ℕ} : Continuous (extGe (n := n) (k := k) (R := 𝔸[K])) := by
  refine continuous_pi fun p => ?_
  simp only [extGe]
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

theorem continuous_supSum (m : ℕ) : Continuous (supSum (K := K) (n := n) m) :=
  continuous_finsetSum _ fun p _ => continuous_apply p

theorem coe_uGL_inv (X : Pos n → 𝔸[K]) :
    (((uGL X)⁻¹ : GL (Fin n) 𝔸[K]) : Matrix (Fin n) (Fin n) 𝔸[K]) = (uMat X).adjugate := by
  rw [Matrix.coe_units_inv, coe_uGL, Matrix.inv_def, det_uMat, Ring.inverse_one, one_smul]

theorem continuous_uGL : Continuous fun X : Pos n → 𝔸[K] => (uGL X : GL (Fin n) 𝔸[K]) := by
  have hc : Continuous fun X : Pos n → 𝔸[K] => uMat X := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [uMat_apply]
    split_ifs
    · exact continuous_const
    · exact continuous_apply _
    · exact continuous_const
  refine Units.continuous_iff.2 ⟨hc, ?_⟩
  simp only [coe_uGL_inv]
  exact hc.matrix_adjugate

def wInt (m : ℕ) (ϕ : AdelicGLn.AdelicGL K n → ℂ) (g : AdelicGLn.AdelicGL K n) (X : Pos n → 𝔸[K]) : ℂ :=
  ϕ (uGL X * g) * (GroundTheory.Global.adelicChar K (-supSum m X) : ℂ)

theorem continuous_wInt (m : ℕ) {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : Continuous ϕ)
    (g : AdelicGLn.AdelicGL K n) : Continuous (wInt m ϕ g) :=
  (hϕ.comp (continuous_uGL.mul continuous_const)).mul
    (continuous_subtype_val.comp (GroundTheory.Global.continuous_adelicChar.comp (continuous_supSum m).neg))

theorem setIntegral_geCols (k : ℕ) (hk : k < n) {H : (Pos n → 𝔸[K]) → ℂ} (hH : Continuous H) :
    ∫ Z in vecDomain K (GePos n k), H (extGe Z) ∂vecMeasure K (GePos n k) =
      ∫ x in vecDomain K (Fin k), ∫ Y in vecDomain K (GePos n (k + 1)),
        H (extGe Y + colX k x) ∂vecMeasure K (GePos n (k + 1)) ∂vecMeasure K (Fin k) := by
  have := setIntegral_vecDomain_sum (colSplit k hk) (hH.comp continuous_extGe)
  simp only [Function.comp_apply, extGe_colSplit] at this
  exact this

theorem partialCoeff_eq_setIntegral {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : Continuous ϕ) :
    ∀ (m k : ℕ), n - k = m → k ≤ n → ∀ g, partialCoeff ϕ k g =
      ∫ Z in vecDomain K (GePos n k), wInt k ϕ g (extGe Z) ∂vecMeasure K (GePos n k) := by
  intro m
  induction m with
  | zero =>
    intro k hkm hk g
    obtain rfl : k = n := by omega
    rw [partialCoeff_self]
    have hz : ∀ Z : GePos k k → 𝔸[K], extGe Z = 0 := fun Z => by
      funext p; rw [extGe, dite_eq_right (by have := p.1.2.2; omega)]; rfl
    simp only [hz, wInt, uGL_zero, one_mul, supSum_zero, neg_zero, AddChar.map_zero_eq_one,
      Circle.coe_one, mul_one]
    rw [setIntegral_const, measureReal_def, vecMeasure_vecDomain, ENNReal.toReal_one, one_smul]
  | succ m ih =>
    intro k hkm hk g
    have hkn : k < n := by omega
    rw [setIntegral_geCols k hkn (continuous_wInt k hϕ g), partialCoeff_of_lt ϕ hkn, stepCoeff,
      vecCoeff]
    refine setIntegral_congr_fun measurableSet_vecDomain fun x _ => ?_
    rw [ih (k + 1) (by omega) hkn, ← integral_mul_const]
    refine integral_congr_ae (ae_of_all _ fun Y => ?_)
    simp only [wInt]
    have hY : ∀ p : Pos n, p.1.2.val ≤ k → extGe Y p = 0 := fun p hp => extGe_eq_zero Y p hp
    have hsup : supSum k (extGe Y) = supSum (k + 1) (extGe Y) := by
      unfold supSum
      refine (Finset.sum_subset (fun p hp => ?_) fun p hp hp' => ?_).symm
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢; omega
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hp'
        exact hY p (by omega)
    have hmul : uGL (extGe Y) * colGL k x = uGL (extGe Y + colX k x) := Units.ext (by
      rw [Units.val_mul, colGL, coe_uGL, coe_uGL, coe_uGL]; exact uMat_mul_uMat_colX hY x)
    rw [← mul_assoc (uGL _), hmul, supSum_add, hsup, supSum_colX k hkn x, neg_add,
      AddChar.map_add_eq_mul, Circle.coe_mul, mul_assoc]

theorem vecCoeff_zero_eq_setIntegral {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : Continuous ϕ) {k : ℕ}
    (hk : k < n) (g : AdelicGLn.AdelicGL K n) :
    vecCoeff (fun x => partialCoeff ϕ (k + 1) (colGL k x * g)) 0 =
      ∫ Z in vecDomain K (GePos n k), wInt (k + 1) ϕ g (extGe Z) ∂vecMeasure K (GePos n k) := by
  rw [setIntegral_geCols k hk (continuous_wInt (k + 1) hϕ g), vecCoeff]
  refine setIntegral_congr_fun measurableSet_vecDomain fun x _ => ?_
  simp only [pair, Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero, neg_zero,
    AddChar.map_zero_eq_one, Circle.coe_one, mul_one]
  rw [partialCoeff_eq_setIntegral hϕ _ (k + 1) rfl hk]
  refine integral_congr_ae (ae_of_all _ fun Y => ?_)
  simp only [wInt]
  have hY : ∀ p : Pos n, p.1.2.val ≤ k → extGe Y p = 0 := fun p hp => extGe_eq_zero Y p hp
  have hmul : uGL (extGe Y) * colGL k x = uGL (extGe Y + colX k x) := Units.ext (by
    rw [Units.val_mul, colGL, coe_uGL, coe_uGL, coe_uGL]; exact uMat_mul_uMat_colX hY x)
  rw [← mul_assoc (uGL _), hmul, supSum_add, supSum_colX_succ, add_zero]

abbrev LowPos (n k : ℕ) : Type := {p : Pos n // k ≤ p.1.1.val}

def lowSplit (k : ℕ) : GePos n k ≃ LowPos n k ⊕ AutomorphicForm.UPos n k where
  toFun p := if h : k ≤ p.1.1.1.val then Sum.inl ⟨p.1, h⟩
    else Sum.inr ⟨p.1.1, by have := p.2; omega, p.2⟩
  invFun := Sum.elim (fun q => ⟨q.1, by have := q.1.2; have := q.2; rw [Fin.lt_def] at *; omega⟩)
    (fun u => ⟨⟨u.1, by have := u.2; rw [Fin.lt_def]; omega⟩, u.2.2⟩)
  left_inv p := by
    by_cases h : k ≤ p.1.1.1.val
    · simp only [dite_eq_left h, Sum.elim_inl]
    · simp only [dite_eq_right h, Sum.elim_inr]
  right_inv q := by
    rcases q with q | u
    · show (if h : k ≤ q.1.1.1.val then _ else _) = _
      rw [dite_eq_left q.2]
      rfl
    · show (if h : k ≤ u.1.1.val then _ else _) = _
      rw [dite_eq_right (by have := u.2; omega)]
      rfl

def extLow {R : Type*} [Zero R] {k : ℕ} (B : LowPos n k → R) : Pos n → R :=
  fun p => if h : k ≤ p.1.1.val then B ⟨p, h⟩ else 0

def extU {R : Type*} [Zero R] {k : ℕ} (A : AutomorphicForm.UPos n k → R) : Pos n → R :=
  fun p => if h : p.1.1.val < k ∧ k ≤ p.1.2.val then A ⟨p.1, h⟩ else 0

theorem extGe_lowSplit {R : Type*} [AddCommGroup R] (k : ℕ) (B : LowPos n k → R)
    (A : AutomorphicForm.UPos n k → R) :
    extGe (fun i => Sum.elim B A (lowSplit k i)) = extLow B + extU A := by
  funext p
  simp only [extGe, extLow, extU, Pi.add_apply]
  by_cases h1 : k ≤ p.1.2.val
  · rw [dite_eq_left h1]
    by_cases h2 : k ≤ p.1.1.val
    · rw [dite_eq_left h2, dite_eq_right (by omega), add_zero]
      show Sum.elim B A (lowSplit k ⟨p, h1⟩) = _
      simp only [lowSplit, Equiv.coe_fn_mk, dite_eq_left h2, Sum.elim_inl]
    · rw [dite_eq_right h2, dite_eq_left ⟨by omega, h1⟩, zero_add]
      show Sum.elim B A (lowSplit k ⟨p, h1⟩) = _
      simp only [lowSplit, Equiv.coe_fn_mk, dite_eq_right h2, Sum.elim_inr]
  · have hp := p.2
    rw [Fin.lt_def] at hp
    rw [dite_eq_right h1, dite_eq_right (by omega), dite_eq_right (by omega), add_zero]

theorem supSum_extU (k : ℕ) (A : AutomorphicForm.UPos n k → 𝔸[K]) :
    supSum (k + 1) (extU A) = 0 := by
  refine Finset.sum_eq_zero fun p hp => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
  rw [extU, dite_eq_right (by omega)]

theorem vecCoeff_zero_eq_setIntegral_low {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : Continuous ϕ)
    {k : ℕ} (hk : k < n) (g : AdelicGLn.AdelicGL K n) :
    vecCoeff (fun x => partialCoeff ϕ (k + 1) (colGL k x * g)) 0 =
      ∫ B in vecDomain K (LowPos n k), (GroundTheory.Global.adelicChar K (-supSum (k + 1) (extLow B)) : ℂ) *
        ∫ A in vecDomain K (AutomorphicForm.UPos n k), ϕ (uGL (extLow B + extU A) * g)
          ∂vecMeasure K (AutomorphicForm.UPos n k) ∂vecMeasure K (LowPos n k) := by
  rw [vecCoeff_zero_eq_setIntegral hϕ hk g]
  have := setIntegral_vecDomain_sum (lowSplit k) ((continuous_wInt (k + 1) hϕ g).comp
    (continuous_extGe (K := K) (n := n) (k := k)))
  simp only [Function.comp_apply, extGe_lowSplit] at this
  rw [this]
  refine setIntegral_congr_fun measurableSet_vecDomain fun B _ => ?_
  simp only [wInt, supSum_add, supSum_extU, add_zero]
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun A => ?_)
  ring

end FourierWhittaker

end

end GroundTheory.Automorphic
end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.AutomorphicForms.FourierWhittaker.Single =====

-- ===== clump member: GroundTheory.AutomorphicForms.FourierWhittaker.PartialCoeffBlockGLEqOfVecMulEq =====
-- clump-header: {"m": "GroundTheory.AutomorphicForms.FourierWhittaker.PartialCoeffBlockGLEqOfVecMulEq", "h": "module\n\npublic import GroundTheory.AutomorphicForms.FourierWhittaker.Smooth\npublic import GroundTheory.AutomorphicForms.FourierWhittaker.AdelicCharPairTorusPtSingle\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Tactic.TypeStar\n\n"}
section -- clump:auto
@[expose] public section

open NumberField NumberField.mixedEmbedding MeasureTheory Topology Set Filter IsDedekindDomain Matrix
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace FourierWhittaker

set_option linter.unusedSectionVars false

open AutomorphicForm

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem stepCoeff_mul_right (k : ℕ) (F : AdelicGLn.AdelicGL K n → ℂ) (g h : AdelicGLn.AdelicGL K n) :
    stepCoeff k F (g * h) = stepCoeff k (fun y => F (y * h)) g := by
  simp only [stepCoeff, mul_assoc]

theorem partialCoeff_mul_right (ϕ : AdelicGLn.AdelicGL K n → ℂ) (k : ℕ) (g h : AdelicGLn.AdelicGL K n) :
    partialCoeff ϕ k (g * h) = partialCoeff (fun y => ϕ (y * h)) k g := by
  unfold partialCoeff
  induction n - k generalizing g with
  | zero => rfl
  | succ m ih =>
    simp only [partialWhittakerCoeff]
    rw [stepCoeff_mul_right]
    congr 1
    funext y
    exact ih y

theorem partialCoeff_mul_finEmb {ϕ : AdelicGLn.AdelicGL K n → ℂ}
    {V : OpenSubgroup (AdelicGLn.FiniteAdelicGL K n)}
    (hV : ∀ g, ∀ v ∈ V, ϕ (g * finEmb K n v) = ϕ g) (k : ℕ) (g : AdelicGLn.AdelicGL K n)
    {v : AdelicGLn.FiniteAdelicGL K n} (hv : v ∈ V) :
    partialCoeff ϕ k (g * finEmb K n v) = partialCoeff ϕ k g := by
  rw [partialCoeff_mul_right]
  congr 2
  funext y
  exact hV y v hv

def iterDeriv (k : ℕ) (g : AdelicGLn.AdelicGL K n) (ϕ : AdelicGLn.AdelicGL K n → ℂ) :
    List (Fin k × BIdx K) → AdelicGLn.AdelicGL K n → ℂ
  | [] => ϕ
  | p :: l => rDeriv (dirY k g p) (iterDeriv k g ϕ l)

theorem IsUSmooth.iterDeriv {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : IsUSmooth ϕ) (k : ℕ)
    (g : AdelicGLn.AdelicGL K n) : ∀ l, IsUSmooth (FourierWhittaker.iterDeriv k g ϕ l)
  | [] => hϕ
  | p :: l => (IsUSmooth.iterDeriv hϕ k g l).rDeriv_smooth _

theorem hasSum_vecCoeff_partialCoeff {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : IsUSmooth ϕ) {k : ℕ}
    (hk : k < n) (g : AdelicGLn.AdelicGL K n)
    (hfin : ∀ (x : Fin k → 𝔸[K]) (z : Fin k → FiniteAdeleRing (𝓞 K) K),
      (∀ i, z i ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K) →
        partialCoeff ϕ (k + 1) (colGL k (x + fun i => GroundTheory.Global.finiteAdeleInr (z i)) * g) =
          partialCoeff ϕ (k + 1) (colGL k x * g)) :
    HasSum (vecCoeff fun x => partialCoeff ϕ (k + 1) (colGL k x * g)) (partialCoeff ϕ (k + 1) g) := by
  classical
  set F : List (Fin k × BIdx K) → (Fin k → 𝔸[K]) → ℂ :=
    fun l x => partialCoeff (iterDeriv k g ϕ l) (k + 1) (colGL k x * g)
  have hsm := hϕ.iterDeriv k g
  have hc : ∀ l, Continuous (F l) := fun l =>
    (continuous_partialCoeff (hsm l).continuous _).comp ((continuous_colGL k).mul continuous_const)
  have hper : ∀ l, ∀ ξ ∈ vecLattice K (Fin k), ∀ x, F l (ξ + x) = F l x := by
    intro l ξ hξ x
    obtain ⟨η, rfl⟩ := mem_vecLattice.1 hξ
    simp only [F]
    rw [colGL_add, mul_assoc, ← diagonal_colGL, partialCoeff_succ_diagonal_colGL (hsm l).left hk]
  have hd : ∀ l p x, HasDerivAt (fun s : ℝ => F l (x + torusPt (Pi.single p s))) (F (p :: l) x) 0 := by
    intro l p x
    have h := hasDerivAt_partialCoeff (hsm l) (dirY k g p) (k + 1) (colGL k x * g)
    have e : (fun s : ℝ => F l (x + torusPt (Pi.single p s))) =
        fun s => partialCoeff (iterDeriv k g ϕ l) (k + 1) (colGL k x * g * oneParam (dirY k g p) s) := by
      funext s
      simp only [F]
      rw [colGL_add, mul_assoc, colGL_torusPt_single_mul k hk, mul_assoc]
    rw [e]
    exact h
  have hsum := summable_vecCoeff_of_deriv F hc hper (fun x z hz => hfin x z hz) hd
  have hip : IsIntegralPeriodic (F []) := ⟨hc [], hper [], fun x z hz => hfin x z hz⟩
  have := hip.hasSum_vecCoeff hsum 0
  simp only [pair_zero, AddChar.map_zero_eq_one, Circle.coe_one, mul_one] at this
  convert this using 1
  · rfl
  · show partialCoeff ϕ (k + 1) g = partialCoeff ϕ (k + 1) (colGL k 0 * g)
    rw [colGL_zero, one_mul]

theorem exists_lastRow_eq {k : ℕ} {ξ : Fin k → K} (hξ : ξ ≠ 0) :
    ∃ γ : GL (Fin k) K, Matrix.vecMul (lastVec k) (γ : Matrix (Fin k) (Fin k) K) = ξ := by
  classical
  obtain ⟨i0, hi0⟩ : ∃ i, ξ i ≠ 0 := by
    by_contra h; push Not at h; exact hξ (funext h)
  have hk : 0 < k := Fin.pos i0
  set last : Fin k := ⟨k - 1, by omega⟩
  set σ := Equiv.swap i0 last
  set M : Matrix (Fin k) (Fin k) K :=
    Matrix.of fun r c => if r = last then ξ (σ c) else if r = c then 1 else 0
  have hM : M.IsLowerTriangular := by
    intro r c hrc
    have hrc' : r < c := hrc
    have hr : r ≠ last := by
      intro h; subst h; have := c.2; rw [Fin.lt_def] at hrc'; simp [last] at hrc'; omega
    simp only [M, Matrix.of_apply, ite_eq_right hr, ite_eq_right (ne_of_lt hrc')]
  have hdetM : M.det = ξ i0 := by
    rw [Matrix.det_of_isLowerTriangular _ hM, Finset.prod_eq_single last]
    · simp [M, σ]
    · intro r _ hr
      simp [M, hr]
    · simp
  set γM := M.submatrix id σ
  have hdet : γM.det ≠ 0 := by
    rw [Matrix.det_permute', hdetM]
    exact mul_ne_zero (by rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]) hi0
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero γM hdet, funext fun c => ?_⟩
  rw [vecMul_lastVec _ _ hk]
  simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, γM, M, last, σ]

def rowCompletion {k : ℕ} (ξ : Fin k → K) : GL (Fin k) K :=
  haveI := Classical.propDecidable (ξ ≠ 0)
  if h : ξ ≠ 0 then (exists_lastRow_eq h).choose else 1

theorem vecMul_rowCompletion {k : ℕ} {ξ : Fin k → K} (hξ : ξ ≠ 0) :
    Matrix.vecMul (lastVec k) ((rowCompletion ξ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) = ξ := by
  unfold rowCompletion
  rw [dite_eq_left hξ]
  exact (exists_lastRow_eq hξ).choose_spec

theorem partialCoeff_blockGL_eq_of_vecMul_eq {ϕ : AdelicGLn.AdelicGL K n → ℂ}
    (hϕ : IsLeftInvariant ϕ) {k : ℕ} (hk : k ≤ n) {γ γ' : GL (Fin k) K}
    (h : Matrix.vecMul (lastVec k) (γ : Matrix (Fin k) (Fin k) K) =
      Matrix.vecMul (lastVec k) (γ' : Matrix (Fin k) (Fin k) K)) (g : AdelicGLn.AdelicGL K n) :
    partialCoeff ϕ k (AdelicGLn.diagonal K n (blockGL hk γ') * g) =
      partialCoeff ϕ k (AdelicGLn.diagonal K n (blockGL hk γ) * g) := by
  have hl : IsLastRowUnit (((γ' * γ⁻¹ : GL (Fin k) K)) : Matrix (Fin k) (Fin k) K) := by
    unfold IsLastRowUnit
    rw [Units.val_mul, ← Matrix.vecMul_vecMul, ← h, Matrix.vecMul_vecMul, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
  have : γ' = (γ' * γ⁻¹) * γ := by group
  rw [this, map_mul, map_mul, mul_assoc]
  exact partialCoeff_diagonal_blockGL hϕ _ k rfl hk _ (Or.inl hl) _

def scalarGL (k : ℕ) : Kˣ →* GL (Fin k) K := Units.map (Matrix.scalar (Fin k) : K →+* _).toMonoidHom

theorem coe_scalarGL (k : ℕ) (u : Kˣ) :
    ((scalarGL k u : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) = Matrix.scalar (Fin k) (u : K) := rfl

theorem matVec_scalar {k : ℕ} (u : K) (x : Fin k → 𝔸[K]) :
    matVec (Matrix.scalar (Fin k) u) x = fun i => algebraMap K 𝔸[K] u * x i := by
  funext i
  rw [matVec_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ (Ne.symm hj)]
  · simp

theorem vecMul_scalar {k : ℕ} (ξ : Fin k → K) (u : K) :
    Matrix.vecMul ξ (Matrix.scalar (Fin k) u) = u • ξ := by
  funext c
  simp [Matrix.vecMul, dotProduct, Matrix.scalar_apply, Matrix.diagonal_apply, mul_comm]

theorem colGL_finiteAdeleInr (k : ℕ) (w : Fin k → FiniteAdeleRing (𝓞 K) K) :
    colGL (n := n) k (fun i => GroundTheory.Global.finiteAdeleInr (w i)) = finEmb K n (colGL k w) := by
  apply (AdelicGLn.prodEquiv K n).injective
  rw [prodEquiv_finEmb]
  refine Prod.ext ?_ ?_
  · apply Units.ext
    refine Matrix.ext fun a b => ?_
    rw [AdelicGLn.prodEquiv_apply_fst]
    simp only [colGL, coe_uGL, uMat_apply, colX_apply, Units.val_one, Matrix.one_apply]
    split_ifs <;> rfl
  · apply Units.ext
    refine Matrix.ext fun a b => ?_
    rw [AdelicGLn.prodEquiv_apply_snd]
    simp only [colGL, coe_uGL, uMat_apply, colX_apply]
    split_ifs <;> rfl

theorem finEmb_mul_eq (g : AdelicGLn.AdelicGL K n) (c : AdelicGLn.FiniteAdelicGL K n) :
    finEmb K n c * g = g * finEmb K n ((AdelicGLn.prodEquiv K n g).2⁻¹ * c *
      (AdelicGLn.prodEquiv K n g).2) := by
  have hg : infEmb K n (archPt g) * finEmb K n (AdelicGLn.prodEquiv K n g).2 = g :=
    infEmb_mul_finEmb g
  set a := archPt g
  set f := (AdelicGLn.prodEquiv K n g).2
  rw [← hg, ← mul_assoc, ← infEmb_mul_finEmb_comm, mul_assoc, mul_assoc, ← map_mul, ← map_mul,
    show c * f = f * (f⁻¹ * c * f) by group]

theorem continuous_colGL_fin (k : ℕ) :
    Continuous fun w : Fin k → FiniteAdeleRing (𝓞 K) K => (colGL (n := n) k w : GL (Fin n) _) := by
  have hc : ∀ (a b : Fin n), Continuous fun x : Fin k → FiniteAdeleRing (𝓞 K) K =>
      uMat (colX (n := n) k x) a b := by
    intro a b
    simp only [uMat_apply, colX_apply]
    by_cases h1 : a = b
    · simp only [h1, ite_true]; exact continuous_const
    · simp only [h1, ite_false]
      by_cases h2 : a < b
      · simp only [h2, dite_true]
        by_cases h3 : b.val = k
        · simp only [h3, dite_true]; exact continuous_apply _
        · simp only [h3, dite_false]; exact continuous_const
      · simp only [h2, dite_false]; exact continuous_const
  refine Units.continuous_iff.2 ⟨continuous_pi fun a => continuous_pi fun b => hc a b, ?_⟩
  have : (fun x : Fin k → FiniteAdeleRing (𝓞 K) K => (((colGL (n := n) k x)⁻¹ : GL (Fin n) _) :
      Matrix (Fin n) (Fin n) _)) = fun x => uMat (colX (n := n) k (-x)) := by
    funext x; rw [← colGL_neg]; rfl
  rw [this]
  exact continuous_pi fun a => continuous_pi fun b => (hc a b).comp continuous_neg

theorem exists_integer_colGL_mem (k : ℕ) (V : OpenSubgroup (AdelicGLn.FiniteAdelicGL K n))
    (f : AdelicGLn.FiniteAdelicGL K n) :
    ∃ δ : 𝓞 K, δ ≠ 0 ∧ ∀ z : Fin k → FiniteAdeleRing (𝓞 K) K,
      (∀ i, z i ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K) →
        f⁻¹ * colGL k (fun i => algebraMap K (FiniteAdeleRing (𝓞 K) K) (algebraMap (𝓞 K) K δ) *
          z i) * f ∈ V := by
  set Θ : (Fin k → FiniteAdeleRing (𝓞 K) K) → AdelicGLn.FiniteAdelicGL K n :=
    fun w => f⁻¹ * colGL k w * f
  have hΘ : Continuous Θ := (continuous_const.mul (continuous_colGL_fin k)).mul continuous_const
  have h0 : Θ 0 = 1 := by simp [Θ, colGL_zero]
  have hW : Θ ⁻¹' (V : Set _) ∈ 𝓝 (0 : Fin k → FiniteAdeleRing (𝓞 K) K) :=
    hΘ.continuousAt.preimage_mem_nhds (by rw [h0]; exact V.isOpen.mem_nhds (one_mem V))
  rw [nhds_pi, Filter.mem_pi] at hW
  obtain ⟨I, -, t, ht, hIt⟩ := hW
  have hU : (⋂ i, t i) ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 K) K) := Filter.iInter_mem.2 ht
  obtain ⟨δ, hδ, hδU⟩ := GroundTheory.Global.exists_forall_mul_mem_of_mem_nhds hU
  refine ⟨δ, hδ, fun z hz => hIt fun i _ => ?_⟩
  exact Set.mem_iInter.1 (hδU (z i) (hz i)) i

theorem hasSum_partialCoeff_of_vecCoeff_zero {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : IsUSmooth ϕ)
    {k : ℕ} (hk : k < n)
    (hcusp : ∀ g, vecCoeff (fun x => partialCoeff ϕ (k + 1) (colGL k x * g)) 0 = 0)
    (g : AdelicGLn.AdelicGL K n) :
    HasSum (fun ξ : {ξ : Fin k → K // ξ ≠ 0} =>
        partialCoeff ϕ k (AdelicGLn.diagonal K n (blockGL hk.le (rowCompletion ξ.1)) * g))
      (partialCoeff ϕ (k + 1) g) := by
  classical
  obtain ⟨V, hV⟩ := hϕ.fin
  obtain ⟨δ, hδ, hδV⟩ := exists_integer_colGL_mem (n := n) k V (AdelicGLn.prodEquiv K n g).2
  have hδK : (algebraMap (𝓞 K) K δ) ≠ 0 := by
    simpa using (RingOfIntegers.coe_ne_zero_iff).2 hδ
  set u : Kˣ := Units.mk0 _ hδK
  have hconj : ∀ w : Fin k → 𝔸[K], colGL k w * AdelicGLn.diagonal K n (blockGL hk.le (scalarGL k u⁻¹)) =
      AdelicGLn.diagonal K n (blockGL hk.le (scalarGL k u⁻¹)) *
        colGL k (fun i => algebraMap K 𝔸[K] u * w i) := by
    intro w
    rw [diagonal_blockGL, colGL_mul_blockGL hk, mulVec_map_inv, ← map_inv, inv_inv, coe_scalarGL,
      matVec_scalar]
  have hfin : ∀ (x : Fin k → 𝔸[K]) (z : Fin k → FiniteAdeleRing (𝓞 K) K),
      (∀ i, z i ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K) →
        partialCoeff ϕ (k + 1) (colGL k (x + fun i => GroundTheory.Global.finiteAdeleInr (z i)) *
          (AdelicGLn.diagonal K n (blockGL hk.le (scalarGL k u⁻¹)) * g)) =
          partialCoeff ϕ (k + 1) (colGL k x *
            (AdelicGLn.diagonal K n (blockGL hk.le (scalarGL k u⁻¹)) * g)) := by
    intro x z hz
    have e1 : (fun i => algebraMap K 𝔸[K] (u : K) * GroundTheory.Global.finiteAdeleInr (z i)) =
        fun i => GroundTheory.Global.finiteAdeleInr (algebraMap K (FiniteAdeleRing (𝓞 K) K)
          (algebraMap (𝓞 K) K δ) * z i) := by
      funext i; rw [GroundTheory.Global.algebraMap_mul_finiteAdeleInr]; rfl
    rw [colGL_add, mul_assoc (colGL k x),
      ← mul_assoc (colGL k fun i => GroundTheory.Global.finiteAdeleInr (z i)), hconj, e1,
      colGL_finiteAdeleInr, mul_assoc (AdelicGLn.diagonal K n _), finEmb_mul_eq, ← mul_assoc,
      ← mul_assoc, partialCoeff_mul_finEmb hV _ _ (hδV z hz), mul_assoc]
  have H := hasSum_vecCoeff_partialCoeff hϕ hk _ hfin
  rw [partialCoeff_succ_diagonal_blockGL hϕ.left hk] at H
  have hsupp : Function.support (vecCoeff fun x => partialCoeff ϕ (k + 1) (colGL k x *
      (AdelicGLn.diagonal K n (blockGL hk.le (scalarGL k u⁻¹)) * g))) ⊆ {ξ | ξ ≠ 0} := by
    intro ξ hξ
    by_contra h0
    apply hξ
    have : ξ = 0 := by simpa using h0
    rw [this]
    exact hcusp _
  rw [← hasSum_subtype_iff_of_support_subset hsupp] at H
  set e : {ξ : Fin k → K // ξ ≠ 0} ≃ {ξ : Fin k → K // ξ ≠ 0} :=
    { toFun := fun ξ => ⟨(u⁻¹ : Kˣ) • ξ.1, fun h => ξ.2 (by simpa using congrArg ((u : Kˣ) • ·) h)⟩
      invFun := fun ξ => ⟨(u : Kˣ) • ξ.1, fun h => ξ.2 (by simpa using congrArg ((u⁻¹ : Kˣ) • ·) h)⟩
      left_inv := fun ξ => Subtype.ext (by simp)
      right_inv := fun ξ => Subtype.ext (by simp) }
  rw [← e.hasSum_iff]
  refine H.congr_fun fun ξ => ?_
  show partialCoeff ϕ k (AdelicGLn.diagonal K n (blockGL hk.le (rowCompletion (e ξ).1)) * g) = _
  have h1 := partialCoeff_diagonal_blockGL_eq_vecCoeff hϕ.left hk (rowCompletion ξ.1)
    (AdelicGLn.diagonal K n (blockGL hk.le (scalarGL k u⁻¹)) * g)
  rw [vecMul_rowCompletion ξ.2] at h1
  rw [Function.comp_apply, ← h1, ← mul_assoc, ← map_mul, ← map_mul]
  refine partialCoeff_blockGL_eq_of_vecMul_eq hϕ.left hk.le ?_ g
  rw [Units.val_mul, ← Matrix.vecMul_vecMul, vecMul_rowCompletion ξ.2, coe_scalarGL, vecMul_scalar,
    vecMul_rowCompletion (e ξ).2]
  rfl

end FourierWhittaker

end

end GroundTheory.Automorphic
end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.AutomorphicForms.FourierWhittaker.PartialCoeffBlockGLEqOfVecMulEq =====

-- ===== clump member: GroundTheory.AutomorphicForms.FourierWhittaker.IsAddFundamentalDomainShearSymm =====
-- clump-header: {"m": "GroundTheory.AutomorphicForms.FourierWhittaker.IsAddFundamentalDomainShearSymm", "h": "module\n\npublic import GroundTheory.AutomorphicForms.FourierWhittaker.Single\nimport GroundTheory.AutomorphicForms.ReductionMeasure\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.CategoryTheory.Countable\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\n\n"}
section -- clump:auto
@[expose] public section

open NumberField NumberField.mixedEmbedding MeasureTheory Topology Set Filter IsDedekindDomain Matrix
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace FourierWhittaker

open AutomorphicForm

variable {K : Type*} [Field K] [NumberField K]

theorem existsUnique_triangular {ι : Type*} [Fintype ι] (ord : ι → ℕ)
    {S : (ι → 𝔸[K]) → (ι → 𝔸[K])} (s : ι → (ι → 𝔸[K]) → 𝔸[K]) (hS : ∀ z i, S z i = z i + s i z)
    (hs : ∀ i z z', (∀ j, ord j < ord i → z j = z' j) → s i z = s i z') (y : ι → 𝔸[K]) :
    ∃! g : vecLattice K ι, S (g +ᵥ y) ∈ vecDomain K ι := by
  classical
  set F := GroundTheory.Global.fundamentalSet K
  set A : (ι → K) → ι → 𝔸[K] := fun l i => algebraMap K 𝔸[K] (l i)

  have hex : ∀ N : ℕ, ∃ l : ι → K, ∀ i, ord i < N → S (A l + y) i ∈ F := by
    intro N
    induction N with
    | zero => exact ⟨0, fun i h => absurd h (Nat.not_lt_zero _)⟩
    | succ N ih =>
      obtain ⟨l, hl⟩ := ih
      choose c hc _ using fun i => GroundTheory.Global.existsUnique_sub_mem_fundamentalSet K (S (A l + y) i)
      set l' : ι → K := fun i => if ord i = N then l i - c i else l i
      have hagree : ∀ i j, ord j < ord i → ord i ≤ N → l' j = l j := by
        intro i j hj hi
        simp only [l', ite_eq_right (show ord j ≠ N by omega)]
      refine ⟨l', fun i hi => ?_⟩
      have hsi : s i (A l' + y) = s i (A l + y) := hs i _ _ fun j hj => by
        simp only [A, Pi.add_apply, hagree i j hj (by omega)]
      rw [hS, hsi]
      by_cases hN : ord i = N
      · simp only [A, Pi.add_apply, l', ite_eq_left hN, map_sub]
        have := hc i
        rw [hS] at this
        convert this using 1
        simp only [A, Pi.add_apply]
        ring
      · simp only [A, Pi.add_apply, l', ite_eq_right hN]
        have := hl i (by omega)
        rwa [hS] at this
  obtain ⟨N, hN⟩ : ∃ N, ∀ i, ord i < N :=
    ⟨Finset.univ.sup ord + 1, fun i => Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i))⟩
  obtain ⟨l, hl⟩ := hex N
  refine ⟨⟨A l, l, rfl⟩, fun i _ => hl i (hN i), ?_⟩

  rintro ⟨_, m, rfl⟩ hm
  have key : ∀ M i, ord i < M → m i = l i := by
    intro M
    induction M with
    | zero => intro i h; exact absurd h (Nat.not_lt_zero _)
    | succ M ih =>
      intro i hi
      have hsi : s i (A m + y) = s i (A l + y) := hs i _ _ fun j hj => by
        simp only [A, Pi.add_apply, ih j (by omega)]
      have h1 := hm i (mem_univ i)
      have h2 := hl i (hN i)
      change S ((fun i => algebraMap K 𝔸[K] (m i)) + y) i ∈ F at h1
      rw [hS] at h1 h2
      rw [show ((fun i => algebraMap K 𝔸[K] (m i)) + y) = A m + y from rfl, hsi] at h1
      obtain ⟨c, -, hcu⟩ := GroundTheory.Global.existsUnique_sub_mem_fundamentalSet K (y i + s i (A l + y))
      have e1 : -m i = -l i := by
        have a1 := hcu (-m i) (by
          simp only [A, Pi.add_apply] at h1
          convert h1 using 1; rw [map_neg]; ring)
        have a2 := hcu (-l i) (by
          simp only [A, Pi.add_apply] at h2
          convert h2 using 1; rw [map_neg]; ring)
        rw [a1, a2]
      exact neg_injective e1
  refine Subtype.ext (funext fun i => ?_)
  show algebraMap K 𝔸[K] (m i) = algebraMap K 𝔸[K] (l i)
  rw [key N i (hN i)]

variable {n : ℕ}

section Shear

variable {k : ℕ} (B : LowPos n k → 𝔸[K])

theorem blockEntry_eq_of_vanishing {X : Matrix (Fin n) (Fin n) 𝔸[K]}
    (hX : ∀ i j : Fin n, ¬ ((i : ℕ) < k ∧ k ≤ (j : ℕ)) → X i j = 0) :
    blockEntry (fun u : UPos n k => X u.1.1 u.1.2) = X := by
  ext i j
  rw [blockEntry_apply]
  split_ifs with h
  · rfl
  · exact (hX i j h).symm

theorem uMat_extLow_apply_of_lt (i j : Fin n) (hj : (j : ℕ) < k) (hi : k ≤ (i : ℕ)) :
    uMat (extLow B) i j = 0 := by
  rw [uMat_apply, ite_eq_right (fun h => by subst h; omega), dite_eq_right (fun h => by rw [Fin.lt_def] at h; omega)]

theorem uMat_extLow_inv_apply_of_lt (i j : Fin n) (hj : (j : ℕ) < k) (hi : k ≤ (i : ℕ)) :
    (((uGL (extLow B))⁻¹ : GL (Fin n) 𝔸[K]) : Matrix (Fin n) (Fin n) 𝔸[K]) i j = 0 := by
  letI : Invertible (uMat (extLow B)) := Units.invertible (uGL (extLow B))
  have hT : (uMat (extLow B)).BlockTriangular (fun c : Fin n => if (c : ℕ) < k then 0 else 1) := by
    intro a b hab
    by_cases ha : (a : ℕ) < k
    · simp only [ha, ite_true] at hab
      split_ifs at hab <;> omega
    · by_cases hb : (b : ℕ) < k
      · exact uMat_extLow_apply_of_lt B a b hb (by omega)
      · simp only [ha, hb, ite_false] at hab
        omega
  have hTi := Matrix.blockTriangular_inv_of_blockTriangular hT
  rw [Matrix.coe_units_inv, coe_uGL]
  exact hTi (by simp only; rw [ite_eq_left hj, ite_eq_right (by omega)]; norm_num)

theorem blockEntry_mul_vanishing {M : Matrix (Fin n) (Fin n) 𝔸[K]}
    (hM : ∀ i j : Fin n, (j : ℕ) < k → k ≤ (i : ℕ) → M i j = 0) (A : UPos n k → 𝔸[K]) :
    ∀ i j : Fin n, ¬ ((i : ℕ) < k ∧ k ≤ (j : ℕ)) → (blockEntry A * M) i j = 0 := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [blockEntry_apply]
  split_ifs with h
  · rw [hM c j (by omega) h.2, mul_zero]
  · rw [zero_mul]

def shear : (UPos n k → 𝔸[K]) ≃+ (UPos n k → 𝔸[K]) where
  toFun A u := (blockEntry A * uMat (extLow B)) u.1.1 u.1.2
  invFun Z u := (blockEntry Z * (((uGL (extLow B))⁻¹ : GL (Fin n) 𝔸[K]) :
    Matrix (Fin n) (Fin n) 𝔸[K])) u.1.1 u.1.2
  left_inv A := by
    funext u
    simp only
    rw [blockEntry_eq_of_vanishing (blockEntry_mul_vanishing (uMat_extLow_apply_of_lt B) A),
      Matrix.mul_assoc, ← coe_uGL, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one,
      blockEntry_apply, dite_eq_left u.2]
  right_inv Z := by
    funext u
    simp only
    rw [blockEntry_eq_of_vanishing (blockEntry_mul_vanishing (uMat_extLow_inv_apply_of_lt B) Z),
      Matrix.mul_assoc, ← coe_uGL, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one,
      blockEntry_apply, dite_eq_left u.2]
  map_add' A A' := by
    funext u
    simp [blockEntry_add, Matrix.add_mul]

end Shear

section Shear2

variable {k : ℕ} (B : LowPos n k → 𝔸[K])

theorem unipMatrix_mul_uMat_extLow (A : UPos n k → 𝔸[K]) :
    unipMatrix A * uMat (extLow B) = uMat (extLow B + extU (shear B A)) := by
  rw [unipMatrix, Matrix.add_mul, Matrix.one_mul]
  ext i j
  have hv := blockEntry_mul_vanishing (uMat_extLow_apply_of_lt B) A i j
  rw [Matrix.add_apply, uMat_apply, uMat_apply]
  by_cases hij : i = j
  · subst hij
    rw [ite_eq_left rfl, ite_eq_left rfl, hv (by omega), add_zero]
  · rw [ite_eq_right hij, ite_eq_right hij]
    by_cases hlt : i < j
    · rw [dite_eq_left hlt, dite_eq_left hlt, Pi.add_apply, extU]
      congr 1
      split_ifs with h
      · rfl
      · exact hv h
    · rw [dite_eq_right hlt, dite_eq_right hlt, zero_add]
      exact hv (fun h => hlt (by rw [Fin.lt_def]; omega))

theorem continuous_blockEntry :
    Continuous (blockEntry (n := n) (r := k) (R := 𝔸[K])) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [blockEntry_apply]
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

theorem continuous_shear : Continuous (shear B) :=
  continuous_pi fun u => (continuous_apply u.1.2).comp ((continuous_apply u.1.1).comp
    (continuous_blockEntry.matrix_mul continuous_const))

theorem continuous_shear_symm : Continuous (shear B).symm :=
  continuous_pi fun u => (continuous_apply u.1.2).comp ((continuous_apply u.1.1).comp
    (continuous_blockEntry.matrix_mul continuous_const))

theorem isAddFundamentalDomain_shear_symm :
    IsAddFundamentalDomain (vecLattice K (UPos n k)) ((shear B).symm '' vecDomain K (UPos n k))
      (vecMeasure K (UPos n k)) := by
  classical
  have himg : (shear B).symm '' vecDomain K (UPos n k) = (shear B) ⁻¹' vecDomain K (UPos n k) := by
    ext A
    constructor
    · rintro ⟨Z, hZ, rfl⟩
      simpa using hZ
    · intro h
      exact ⟨shear B A, h, by simp⟩
  rw [himg]
  refine IsAddFundamentalDomain.mk' ((measurableSet_vecDomain.preimage
    (continuous_shear B).measurable).nullMeasurableSet) fun y => ?_
  refine existsUnique_triangular (fun u : UPos n k => u.1.2.val)
    (fun u z => ∑ c ∈ Finset.univ.erase u.1.2, blockEntry z u.1.1 c * uMat (extLow B) c u.1.2)
    (fun z u => ?_) (fun u z z' hzz' => ?_) y
  · show (blockEntry z * uMat (extLow B)) u.1.1 u.1.2 = _
    rw [Matrix.mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ u.1.2), blockEntry_apply,
      dite_eq_left u.2, uMat_apply, ite_eq_left rfl, mul_one]
  · refine Finset.sum_congr rfl fun c hc => ?_
    by_cases hcu : c < u.1.2
    · rw [blockEntry_apply, blockEntry_apply]
      split_ifs with h
      · rw [hzz' ⟨(u.1.1, c), h⟩ (by rw [Fin.lt_def] at hcu; exact hcu)]
      · rfl
    · have hne : c ≠ u.1.2 := Finset.ne_of_mem_erase hc
      have : uMat (extLow B) c u.1.2 = 0 := by
        rw [uMat_apply, ite_eq_right hne, dite_eq_right (fun h => hcu (by
          rw [Fin.lt_def] at h ⊢; have := Fin.val_injective.ne hne; omega))]
      rw [this, mul_zero, mul_zero]

theorem setIntegral_uGL_extLow_extU {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : IsLeftInvariant ϕ)
    (g : AdelicGLn.AdelicGL K n) :
    ∫ A in vecDomain K (UPos n k), ϕ (uGL (extLow B + extU A) * g) ∂vecMeasure K (UPos n k) =
      constantTerm k ϕ (uGL (extLow B) * g) := by
  have hrepr : ∀ A, uGL (extLow B + extU A) = unipGL ((shear B).symm A) * uGL (extLow B) := by
    intro A
    refine Units.ext ?_
    rw [Units.val_mul, coe_unipGL, coe_uGL, coe_uGL, unipMatrix_mul_uMat_extLow,
      AddEquiv.apply_symm_apply]
  simp_rw [hrepr, mul_assoc]
  rw [setIntegral_comp_addEquiv (shear B).symm (continuous_shear_symm B) (continuous_shear B)
    (isAddFundamentalDomain_shear_symm B) (f := fun A => ϕ (unipGL A * (uGL (extLow B) * g)))
    fun ξ hξ x => hϕ.unipGL_vadd _ ⟨ξ, hξ⟩ x]
  rfl

end Shear2

theorem vecCoeff_zero_of_isCuspidal {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hc : Continuous ϕ)
    (hl : IsLeftInvariant ϕ) (hcusp : IsCuspidal ϕ) {k : ℕ} (hk0 : 0 < k) (hk : k < n)
    (g : AdelicGLn.AdelicGL K n) :
    vecCoeff (fun x => partialCoeff ϕ (k + 1) (colGL k x * g)) 0 = 0 := by
  rw [vecCoeff_zero_eq_setIntegral_low hc hk g]
  refine (setIntegral_congr_fun measurableSet_vecDomain fun B _ => ?_).trans (integral_zero _ _)
  rw [setIntegral_uGL_extLow_extU B hl g, hcusp k hk0 hk, mul_zero]

end FourierWhittaker

end

end GroundTheory.Automorphic
end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.AutomorphicForms.FourierWhittaker.IsAddFundamentalDomainShearSymm =====

-- ===== clump member: GroundTheory.AutomorphicForms.FourierWhittaker =====
-- clump-header: {"m": "GroundTheory.AutomorphicForms.FourierWhittaker", "h": "module\n\npublic import GroundTheory.AutomorphicForms.FourierWhittaker.IsAddFundamentalDomainImageOfMapVecLattice\npublic import GroundTheory.AutomorphicForms.FourierWhittaker.Series\npublic import GroundTheory.AutomorphicForms.FourierWhittaker.AlgebraMapIntegerMemIntegralFiniteAdeles\npublic import GroundTheory.AutomorphicForms.FourierWhittaker.AdelicCharPairTorusPtSingle\npublic import GroundTheory.AutomorphicForms.FourierWhittaker.UMatColXEqFromBlocks\npublic import GroundTheory.AutomorphicForms.FourierWhittaker.PartialCoeffDiagonalBlockGLEqVecCoeff\npublic import GroundTheory.AutomorphicForms.FourierWhittaker.Smooth\npublic import GroundTheory.AutomorphicForms.FourierWhittaker.PartialCoeffBlockGLEqOfVecMulEq\npublic import GroundTheory.AutomorphicForms.FourierWhittaker.Single\npublic import GroundTheory.AutomorphicForms.FourierWhittaker.IsAddFundamentalDomainShearSymm\nimport GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Uniform\nimport GroundTheory.AutomorphicForms.ReductionMeasure\nimport GroundTheory.GlobalFields.Adele.Topology\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

open NumberField NumberField.mixedEmbedding MeasureTheory Topology Set Filter IsDedekindDomain Matrix
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace FourierWhittaker

open AutomorphicForm

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

def whittaker (ϕ : AdelicGLn.AdelicGL K n → ℂ) (g : AdelicGLn.AdelicGL K n) : ℂ :=
  ∫ X in vecDomain K (Pos n), ϕ (uGL X * g) * (GroundTheory.Global.adelicChar K (-supSum 0 X) : ℂ)
    ∂vecMeasure K (Pos n)

def gePosZeroEquiv : GePos n 0 ≃ Pos n := Equiv.subtypeUnivEquiv fun _ => Nat.zero_le _

theorem whittaker_eq_partialCoeff_zero {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : Continuous ϕ)
    (g : AdelicGLn.AdelicGL K n) : whittaker ϕ g = partialCoeff ϕ 0 g := by
  rw [partialCoeff_eq_setIntegral hϕ _ 0 rfl (Nat.zero_le n), whittaker]
  let E := MeasurableEquiv.piCongrLeft (fun _ : Pos n => 𝔸[K]) (gePosZeroEquiv (n := n))
  have hE : MeasurePreserving E (vecMeasure K (GePos n 0)) (vecMeasure K (Pos n)) :=
    measurePreserving_piCongrLeft (fun _ : Pos n => GroundTheory.Global.adeleMeasure K) gePosZeroEquiv
  have hext : ∀ Z : GePos n 0 → 𝔸[K], extGe Z = E Z := by
    intro Z
    funext p
    rw [extGe, dite_eq_left (Nat.zero_le _)]
    simp [E, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, gePosZeroEquiv]
  have hpre : E ⁻¹' vecDomain K (Pos n) = vecDomain K (GePos n 0) := by
    ext Z
    simp only [Set.mem_preimage, vecDomain, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h q
      have := h (gePosZeroEquiv q)
      simpa [E, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, gePosZeroEquiv] using this
    · intro h p
      have := h (gePosZeroEquiv.symm p)
      simpa [E, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, gePosZeroEquiv] using this
  rw [← hE.setIntegral_preimage_emb E.measurableEmbedding, hpre]
  refine setIntegral_congr_fun measurableSet_vecDomain fun Z _ => ?_
  simp only [wInt, hext]

theorem stepCoeff_zero (F : AdelicGLn.AdelicGL K n → ℂ) (g : AdelicGLn.AdelicGL K n) :
    stepCoeff 0 F g = F g := by
  have hx : ∀ x : Fin 0 → 𝔸[K], x = 0 := fun x => funext fun i => i.elim0
  have hc : ∀ x : Fin 0 → 𝔸[K], F (colGL 0 x * g) *
      (GroundTheory.Global.adelicChar K (-pair (lastVec 0) x) : ℂ) = F g := by
    intro x
    rw [hx x, colGL_zero, one_mul, pair_zero, neg_zero, AddChar.map_zero_eq_one, Circle.coe_one,
      mul_one]
  rw [stepCoeff, vecCoeff]
  simp_rw [hc]
  rw [setIntegral_const, measureReal_def, vecMeasure_vecDomain, ENNReal.toReal_one, one_smul]

theorem partialCoeff_zero_eq_one (ϕ : AdelicGLn.AdelicGL K n → ℂ) (hn : 0 < n) :
    partialCoeff ϕ 0 = partialCoeff ϕ 1 := by
  funext g
  rw [partialCoeff_of_lt ϕ hn, stepCoeff_zero]

theorem whittaker_eq_partialCoeff {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : Continuous ϕ) (hn : 0 < n)
    (g : AdelicGLn.AdelicGL K n) : whittaker ϕ g = partialCoeff ϕ 1 g := by
  rw [whittaker_eq_partialCoeff_zero hϕ, partialCoeff_zero_eq_one ϕ hn]

theorem isUSmooth_of_isAutomorphicForm {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : IsAutomorphicForm ϕ) :
    IsUSmooth ϕ := by
  obtain ⟨U, -, hU⟩ := exists_openSubgroup_rightInvariant hϕ.isSmooth hϕ.isKFinite
  exact ⟨hϕ.isSmooth.1, ⟨U, hU⟩, hϕ.isLeftInvariant⟩

theorem hasSum_partialCoeff_cusp {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : ϕ ∈ cuspForms K n) {k : ℕ}
    (hk0 : 0 < k) (hk : k < n) (g : AdelicGLn.AdelicGL K n) :
    HasSum (fun ξ : {ξ : Fin k → K // ξ ≠ 0} =>
        partialCoeff ϕ k (AdelicGLn.diagonal K n (blockGL hk.le (rowCompletion ξ.1)) * g))
      (partialCoeff ϕ (k + 1) g) := by
  have hzero (g' : AdelicGLn.AdelicGL K n) :
      vecCoeff (fun x => partialCoeff ϕ (k + 1) (colGL k x * g')) 0 = 0 := by
    have hconstant (B : LowPos n k → 𝔸[K]) :
        ∫ A in vecDomain K (UPos n k), ϕ (uGL (extLow B + extU A) * g')
            ∂vecMeasure K (UPos n k) = constantTerm k ϕ (uGL (extLow B) * g') := by
      have hrepr (A : UPos n k → 𝔸[K]) :
          uGL (extLow B + extU A) = unipGL ((shear B).symm A) * uGL (extLow B) := by
        apply Units.ext
        rw [Units.val_mul, coe_unipGL, coe_uGL, coe_uGL, unipMatrix_mul_uMat_extLow,
          AddEquiv.apply_symm_apply]
      simp_rw [hrepr, mul_assoc]
      rw [setIntegral_comp_addEquiv (shear B).symm (continuous_shear_symm B) (continuous_shear B)
        (isAddFundamentalDomain_shear_symm B) (f := fun A => ϕ (unipGL A * (uGL (extLow B) * g')))
        fun ξ hξ x => hϕ.1.isLeftInvariant.unipGL_vadd _ ⟨ξ, hξ⟩ x]
      rfl
    rw [vecCoeff_zero_eq_setIntegral_low hϕ.1.continuous hk g']
    refine (setIntegral_congr_fun measurableSet_vecDomain fun B _ => ?_).trans (integral_zero _ _)
    rw [hconstant B, hϕ.2 k hk0 hk, mul_zero]
  exact hasSum_partialCoeff_of_vecCoeff_zero (isUSmooth_of_isAutomorphicForm hϕ.1) hk hzero g


variable (K) in
def mirabolic (k : ℕ) : Subgroup (GL (Fin k) K) where
  carrier := {h | IsLastRowUnit ((h : GL (Fin k) K) : Matrix (Fin k) (Fin k) K)}
  one_mem' := by
    show Matrix.vecMul (lastVec k) (1 : Matrix (Fin k) (Fin k) K) = lastVec k
    rw [Matrix.vecMul_one]
  mul_mem' {a b} ha hb := by
    show Matrix.vecMul (lastVec k) ((a * b : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) = lastVec k
    rw [Units.val_mul, ← Matrix.vecMul_vecMul, ha, hb]
  inv_mem' {a} ha := IsLastRowUnit.inv ha

def lastRow {k : ℕ} (γ : GL (Fin k) K) : Fin k → K :=
  Matrix.vecMul (lastVec k) (γ : Matrix (Fin k) (Fin k) K)

theorem lastRow_ne_zero {k : ℕ} (hk : 0 < k) (γ : GL (Fin k) K) : lastRow γ ≠ 0 := by
  intro h
  have hlv : lastVec (K := K) k ≠ 0 := fun h0 => by
    have := congrFun h0 ⟨k - 1, by omega⟩
    simp [lastVec] at this; omega
  apply hlv
  have := congrArg (fun v => Matrix.vecMul v ((γ⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K)) h
  simp only [lastRow, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.vecMul_one, Matrix.zero_vecMul] at this
  exact this

theorem lastRow_eq_iff {k : ℕ} (γ γ' : GL (Fin k) K) :
    lastRow γ = lastRow γ' ↔ γ' * γ⁻¹ ∈ mirabolic K k := by
  constructor
  · intro h
    show Matrix.vecMul (lastVec k) ((γ' * γ⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) = lastVec k
    rw [Units.val_mul, ← Matrix.vecMul_vecMul]
    change Matrix.vecMul (lastRow γ') _ = _
    rw [← h, lastRow, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.vecMul_one]
  · intro h
    have h' : Matrix.vecMul (lastVec k) ((γ' * γ⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) =
        lastVec k := h
    symm
    calc lastRow γ' = lastRow ((γ' * γ⁻¹) * γ) := by rw [inv_mul_cancel_right]
      _ = Matrix.vecMul (Matrix.vecMul (lastVec k) ((γ' * γ⁻¹ : GL (Fin k) K) :
            Matrix (Fin k) (Fin k) K)) (γ : Matrix (Fin k) (Fin k) K) := by
          rw [lastRow, Units.val_mul, ← Matrix.vecMul_vecMul]
      _ = lastRow γ := by rw [h']; rfl

def cosetEquiv {k : ℕ} (hk : 0 < k) :
    Quotient (QuotientGroup.rightRel (mirabolic K k)) ≃ {ξ : Fin k → K // ξ ≠ 0} where
  toFun := Quotient.lift (fun γ => ⟨lastRow γ, lastRow_ne_zero hk γ⟩) fun a b hab =>
    Subtype.ext ((lastRow_eq_iff a b).2 (QuotientGroup.rightRel_apply.1 hab))
  invFun ξ := Quotient.mk _ (rowCompletion ξ.1)
  left_inv := by
    refine Quotient.ind fun γ => Quotient.sound ?_
    show (QuotientGroup.rightRel (mirabolic K k)) (rowCompletion (lastRow γ)) γ
    rw [QuotientGroup.rightRel_apply, ← lastRow_eq_iff]
    exact vecMul_rowCompletion (lastRow_ne_zero hk γ)
  right_inv ξ := Subtype.ext (vecMul_rowCompletion ξ.2)

theorem hasSum_partialCoeff_cusp_cosets {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : ϕ ∈ cuspForms K n)
    {k : ℕ} (hk0 : 0 < k) (hk : k < n) (g : AdelicGLn.AdelicGL K n) :
    HasSum (fun c : Quotient (QuotientGroup.rightRel (mirabolic K k)) =>
        partialCoeff ϕ k (AdelicGLn.diagonal K n (blockGL hk.le c.out) * g))
      (partialCoeff ϕ (k + 1) g) := by
  rw [← (cosetEquiv (K := K) hk0).symm.hasSum_iff]
  refine (hasSum_partialCoeff_cusp hϕ hk0 hk g).congr_fun fun ξ => ?_
  simp only [Function.comp_apply]
  refine partialCoeff_blockGL_eq_of_vecMul_eq hϕ.1.isLeftInvariant hk.le ?_ g
  have hc : ((cosetEquiv (K := K) hk0).symm ξ) = Quotient.mk _ (rowCompletion ξ.1) := rfl
  have hrel := Quotient.mk_out (s := QuotientGroup.rightRel (mirabolic K k)) (rowCompletion ξ.1)
  rw [hc]
  have := (lastRow_eq_iff _ _).2 (QuotientGroup.rightRel_apply.1 hrel)
  exact this.symm

def nestedWhittaker (ϕ : AdelicGLn.AdelicGL K n → ℂ) : ℕ → AdelicGLn.AdelicGL K n → ℂ
  | 0 => whittaker ϕ
  | 1 => whittaker ϕ
  | k + 2 => fun g => if h : k + 1 < n then
      ∑' c : Quotient (QuotientGroup.rightRel (mirabolic K (k + 1))),
        nestedWhittaker ϕ (k + 1) (AdelicGLn.diagonal K n (blockGL h.le c.out) * g)
    else 0

theorem partialCoeff_eq_nestedWhittaker {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : ϕ ∈ cuspForms K n) :
    ∀ k, 0 < k → k ≤ n → partialCoeff ϕ k = nestedWhittaker ϕ k := by
  intro k
  induction k with
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | succ k ih =>
    intro _ hkn
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · funext g
      exact (whittaker_eq_partialCoeff hϕ.1.continuous hkn g).symm
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      funext g
      have hlt : m + 1 < n := by omega
      rw [nestedWhittaker]
      dsimp only
      rw [dite_eq_left hlt, ← (hasSum_partialCoeff_cusp_cosets hϕ hk0 hlt g).tsum_eq, ih hk0 hlt.le]

theorem eq_nestedWhittaker {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : ϕ ∈ cuspForms K n) (hn : 0 < n)
    (g : AdelicGLn.AdelicGL K n) : ϕ g = nestedWhittaker ϕ n g := by
  rw [← partialCoeff_eq_nestedWhittaker hϕ n hn le_rfl, partialCoeff_self]

end FourierWhittaker

end

end GroundTheory.Automorphic
end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.AutomorphicForms.FourierWhittaker =====
