module

public import GroundTheory.GlobalFields.ComplexMultiplication.BaseChangeGalois
public import GroundTheory.GlobalFields.ComplexMultiplication.DifferentialConstantField
public import Mathlib.Basic.Complex.Basic
public import GroundTheory.GlobalFields.ComplexMultiplication.AlgebraicityHom
public import GroundTheory.GlobalFields.ComplexMultiplication.AutCFixed
public import GroundTheory.GlobalFields.ComplexMultiplication.BaseChangeDegree
public import GroundTheory.GlobalFields.ComplexMultiplication.BaseChangeField
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import GroundTheory.GlobalFields.ComplexMultiplication.DualDescent
public import GroundTheory.GlobalFields.ComplexMultiplication.InseparableFrobenius
public import GroundTheory.GlobalFields.ComplexMultiplication.ReductionIsogenyMap
public import GroundTheory.GlobalFields.ComplexMultiplication.GoodReductionAlmostAll
public import GroundTheory.GlobalFields.ComplexMultiplication.InseparableFrobeniusFactor
public import GroundTheory.GlobalFields.ComplexMultiplication.IsogenyDegreeOne
public import GroundTheory.GlobalFields.ComplexMultiplication.ReductionDegree
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import GroundTheory.GlobalFields.ComplexMultiplication.AlgebraicityGalois
public import GroundTheory.GlobalFields.ComplexMultiplication.PrimeLocalization
public import GroundTheory.GlobalFields.SemilocalAlgebras.Galois
public import GroundTheory.GlobalFields.TateThesis.DegreeOnePrimes
public import Mathlib.RingTheory.Frobenius
public import GroundTheory.GlobalFields.ComplexMultiplication.BadPrimesFinite
public import GroundTheory.GlobalFields.ComplexMultiplication.FrobeniusAtPrimesIsogeny
import GroundTheory.GlobalFields.ComplexMultiplication.BaseChangeDescent
import GroundTheory.GlobalFields.ComplexMultiplication.JInvariantSurjective

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: GroundTheory.GlobalFields.ComplexMultiplication.ReductionDifferential, GroundTheory.GlobalFields.ComplexMultiplication.AlgebraicityDescent, GroundTheory.GlobalFields.ComplexMultiplication.FrobeniusAtPrimesLocal, GroundTheory.GlobalFields.ComplexMultiplication.FrobeniusAtPrimes

-- ===== clump member: GroundTheory.GlobalFields.ComplexMultiplication.ReductionDifferential =====
-- clump-header: {"m": "GroundTheory.GlobalFields.ComplexMultiplication.ReductionDifferential", "h": "module\n\npublic import GroundTheory.GlobalFields.ComplexMultiplication.DifferentialConstantField\npublic import GroundTheory.GlobalFields.ComplexMultiplication.ReductionIsogenyMap\npublic import Mathlib.Algebra.TrivSqZeroExt.Basic\nimport GroundTheory.GlobalFields.ComplexMultiplication.ReductionComp\npublic import GroundTheory.GlobalFields.ComplexMultiplication.ReductionDegree\n\n"}
section -- clump:auto
@[expose] public section

namespace GroundTheory.Global

noncomputable section

open IsLocalRing Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian KaehlerDifferential
open scoped Polynomial.Bivariate

universe u

section Delta

variable {F : Type u} [Field F] (E : WeierstrassCurve F) [E.IsElliptic]

def invDeriv (f : E.toAffine.FunctionField) : E.toAffine.FunctionField :=
  invCoeff E (D F E.toAffine.FunctionField f)

theorem invCoeff_smul_mul (c : E.toAffine.FunctionField) (η : KaehlerDifferential F E.toAffine.FunctionField) :
    invCoeff E (c • η) = c * invCoeff E η :=
  invCoeff_eq E (by rw [mul_smul, invCoeff_smul])

theorem invDeriv_add (f g : E.toAffine.FunctionField) :
    invDeriv E (f + g) = invDeriv E f + invDeriv E g := by
  rw [invDeriv, map_add (f := _), invCoeff_add]; rfl

theorem invDeriv_mul (f g : E.toAffine.FunctionField) :
    invDeriv E (f * g) = f * invDeriv E g + g * invDeriv E f := by
  rw [invDeriv, Derivation.leibniz, invCoeff_add, invCoeff_smul_mul, invCoeff_smul_mul]; rfl

theorem invDeriv_algebraMap (c : F) : invDeriv E (algebraMap F _ c) = 0 := by
  rw [invDeriv, D_coeff, invCoeff_zero]

theorem invDeriv_genX : invDeriv E (genX E) = 2 * genY E +
    algebraMap F _ E.a₁ * genX E + algebraMap F _ E.a₃ := by
  apply invCoeff_eq
  exact (omegaAt_some_spec E _).1

theorem invDeriv_genY : invDeriv E (genY E) = 3 * genX E ^ 2 +
    2 * algebraMap F _ E.a₂ * genX E + algebraMap F _ E.a₄ - algebraMap F _ E.a₁ * genY E := by
  apply invCoeff_eq
  exact (omegaAt_some_spec E _).2

variable {E} {E' : WeierstrassCurve F} [E'.IsElliptic]

theorem isogCoeff_mul (φ : Isogeny E E') {x y : E.toAffine.FunctionField}
    {h : (E'.baseChange E.toAffine.FunctionField).toAffine.Nonsingular x y}
    (hφ : φ.1 = Point.some x y h) :
    isogCoeff φ * (2 * y + algebraMap F _ E'.a₁ * x + algebraMap F _ E'.a₃) = invDeriv E x := by
  have e := (omegaAt_some_spec E' h).1
  rw [← hφ, ← isogenyPullback_invariantDifferential, isogenyPullback_invariantDifferential_eq_smul,
    smul_smul] at e
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃] at e
  rw [invDeriv, invCoeff_eq E e]
  ring

end Delta

section Dual

open TrivSqZeroExt

def dualMap {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    TrivSqZeroExt R R →+* TrivSqZeroExt S S where
  toFun z := inl (f z.fst) + inr (f z.snd)
  map_one' := by ext <;> simp
  map_mul' a b := by
    ext <;> simp [fst_mul, snd_mul, MulOpposite.smul_eq_mul_unop]
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp

theorem dualMap_fst {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (z : TrivSqZeroExt R R) : (dualMap f z).fst = f z.fst := by simp [dualMap]

theorem dualMap_snd {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (z : TrivSqZeroExt R R) : (dualMap f z).snd = f z.snd := by simp [dualMap]

variable {F : Type u} [Field F] (E : WeierstrassCurve F) [E.IsElliptic]

def invDerivHom : E.toAffine.FunctionField →+*
    TrivSqZeroExt E.toAffine.FunctionField E.toAffine.FunctionField where
  toFun f := inl f + inr (invDeriv E f)
  map_one' := by
    have h1 : invDeriv E 1 = 0 := by
      rw [← map_one (algebraMap F E.toAffine.FunctionField), invDeriv_algebraMap]
    ext <;> simp [h1]
  map_mul' a b := by
    ext <;> simp [fst_mul, snd_mul, MulOpposite.smul_eq_mul_unop, invDeriv_mul]
    ring
  map_zero' := by
    have h0 : invDeriv E 0 = 0 := by
      simpa using invDeriv_algebraMap E 0
    ext <;> simp [h0]
  map_add' a b := by ext <;> simp [invDeriv_add]

theorem invDerivHom_fst (f : E.toAffine.FunctionField) : (invDerivHom E f).fst = f := by
  simp [invDerivHom]

theorem invDerivHom_snd (f : E.toAffine.FunctionField) :
    (invDerivHom E f).snd = invDeriv E f := by
  simp [invDerivHom]

end Dual

section Gauss

open TrivSqZeroExt

variable {𝒪 : Type u} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (W : WeierstrassCurve 𝒪)

def gaussDX : gaussRing W :=
  2 * gaussY W + algebraMap 𝒪 _ W.a₁ * gaussX W + algebraMap 𝒪 _ W.a₃

def gaussDY : gaussRing W :=
  3 * gaussX W ^ 2 + 2 * algebraMap 𝒪 _ W.a₂ * gaussX W + algebraMap 𝒪 _ W.a₄ -
    algebraMap 𝒪 _ W.a₁ * gaussY W

theorem gauss_equation (K : Type u) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] :
    (W.map (algebraMap 𝒪 (gaussRing W))).toAffine.Equation (gaussX W) (gaussY W) := by
  have h := equation_gen (W.baseChange K)
  rw [← algebraMap_gaussX W K, ← algebraMap_gaussY W K] at h
  have e : (W.baseChange K).baseChange (W.baseChange K).toAffine.FunctionField =
      (W.map (algebraMap 𝒪 (gaussRing W))).map (algebraMap (gaussRing W) _) :=
    (gaussCurve_map_functionField K W W).symm
  rw [e] at h
  exact (WeierstrassCurve.Affine.map_equation (W.map (algebraMap 𝒪 (gaussRing W))).toAffine
    (IsFractionRing.injective _ (W.baseChange K).toAffine.FunctionField) _ _).mp h

theorem gauss_dual_equation (K : Type u) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] :
    (W.map ((inlHom (gaussRing W) (gaussRing W)).comp (algebraMap 𝒪 (gaussRing W)))).toAffine.Equation
      (inl (gaussX W) + inr (gaussDX W)) (inl (gaussY W) + inr (gaussDY W)) := by
  have e := (WeierstrassCurve.Affine.equation_iff _ _).1 (gauss_equation W K)
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at e
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, RingHom.comp_apply, inlHom_apply]
  ext
  · simp only [fst_add, fst_mul, fst_pow, fst_inl, fst_inr, add_zero]
    linear_combination e
  · simp only [fst_add, fst_mul, fst_pow, fst_inl, fst_inr, snd_add, snd_mul, snd_pow, snd_inl,
      snd_inr, add_zero, zero_add, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op,
      nsmul_eq_mul, Nat.cast_ofNat, Nat.pred_eq_sub_one, zero_mul]
    simp only [gaussDX, gaussDY]
    norm_num
    ring

end Gauss

section GaussDeriv

open TrivSqZeroExt

variable {𝒪 : Type u} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type u) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W : WeierstrassCurve 𝒪)

def gaussDualA : W.toAffine.CoordinateRing →+* TrivSqZeroExt (gaussRing W) (gaussRing W) :=
  AdjoinRoot.lift (eval₂RingHom ((inlHom (gaussRing W) (gaussRing W)).comp
      (algebraMap 𝒪 (gaussRing W))) (inl (gaussX W) + inr (gaussDX W)))
    (inl (gaussY W) + inr (gaussDY W))
    (eval₂_polynomial_of_equation W _ (gauss_dual_equation W K))

theorem gaussDualA_algebraMap (c : 𝒪) :
    gaussDualA K W (algebraMap 𝒪 _ c) = inl (algebraMap 𝒪 (gaussRing W) c) := by
  rw [IsScalarTower.algebraMap_apply 𝒪 𝒪[X] W.toAffine.CoordinateRing, AdjoinRoot.algebraMap_eq,
    gaussDualA, AdjoinRoot.lift_of]
  simp

theorem gaussDualA_X :
    gaussDualA K W (CoordinateRing.mk W (C X)) = inl (gaussX W) + inr (gaussDX W) := by
  rw [AdjoinRoot.mk_C, gaussDualA, AdjoinRoot.lift_of]
  simp

theorem gaussDualA_Y :
    gaussDualA K W (CoordinateRing.mk W Y) = inl (gaussY W) + inr (gaussDY W) := by
  rw [AdjoinRoot.mk_X, gaussDualA, AdjoinRoot.lift_root]

theorem fst_gaussDualA (a : W.toAffine.CoordinateRing) :
    (gaussDualA K W a).fst = algebraMap _ (gaussRing W) a := by
  have : ((fstHom 𝒪 (gaussRing W) (gaussRing W)).toRingHom).comp (gaussDualA K W) =
      algebraMap _ (gaussRing W) := by
    apply coordinateRing_ringHom_ext
    · intro c
      simp [gaussDualA_algebraMap, ← IsScalarTower.algebraMap_apply]
    · show (gaussDualA K W (CoordinateRing.mk W (C X))).fst = _
      rw [gaussDualA_X, fst_add, fst_inl, fst_inr, add_zero]; rfl
    · show (gaussDualA K W (CoordinateRing.mk W Y)).fst = _
      rw [gaussDualA_Y, fst_add, fst_inl, fst_inr, add_zero]; rfl
  exact congrArg (fun f => f a) this

def gaussDual : gaussRing W →+* TrivSqZeroExt (gaussRing W) (gaussRing W) :=
  IsLocalization.lift (M := (gaussPrime W).primeCompl) (S := gaussRing W) (g := gaussDualA K W)
    fun s => isUnit_iff_isUnit_fst.2 (by
      rw [fst_gaussDualA]; exact IsLocalization.map_units (gaussRing W) s)

theorem gaussDual_algebraMap (a : W.toAffine.CoordinateRing) :
    gaussDual K W (algebraMap _ _ a) = gaussDualA K W a :=
  IsLocalization.lift_eq _ _

theorem gaussDual_algebraMap_base (c : 𝒪) :
    gaussDual K W (algebraMap 𝒪 (gaussRing W) c) = inl (algebraMap 𝒪 (gaussRing W) c) := by
  rw [IsScalarTower.algebraMap_apply 𝒪 W.toAffine.CoordinateRing (gaussRing W),
    gaussDual_algebraMap, gaussDualA_algebraMap, ← IsScalarTower.algebraMap_apply]

def gaussDeriv (g : gaussRing W) : gaussRing W := (gaussDual K W g).snd

end GaussDeriv

section Compat

open TrivSqZeroExt

variable {𝒪 : Type u} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type u) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W : WeierstrassCurve 𝒪)
  [W.IsElliptic]

theorem algebraMap_gauss_const (c : 𝒪) :
    algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField (algebraMap 𝒪 _ c) =
      algebraMap K _ (algebraMap 𝒪 K c) := by
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply 𝒪 K]

theorem algebraMap_gaussDeriv (g : gaussRing W) :
    algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField (gaussDeriv K W g) =
      invDeriv (W.baseChange K) (algebraMap (gaussRing W) _ g) := by
  have key : (dualMap (algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField)).comp
      (gaussDual K W) = (invDerivHom (W.baseChange K)).comp (algebraMap (gaussRing W) _) := by
    apply IsLocalization.ringHom_ext (gaussPrime W).primeCompl
    apply coordinateRing_ringHom_ext
    · intro c
      simp only [RingHom.comp_apply,
        ← IsScalarTower.algebraMap_apply 𝒪 W.toAffine.CoordinateRing (gaussRing W),
        gaussDual_algebraMap_base]
      ext
      · rw [dualMap_fst, invDerivHom_fst, fst_inl]
      · rw [dualMap_snd, invDerivHom_snd, snd_inl, map_zero, algebraMap_gauss_const,
          invDeriv_algebraMap]
    · simp only [RingHom.comp_apply, gaussDual_algebraMap, gaussDualA_X]
      rw [show algebraMap W.toAffine.CoordinateRing (gaussRing W) (CoordinateRing.mk W (C X)) =
        gaussX W from rfl, algebraMap_gaussX]
      ext
      · rw [dualMap_fst, invDerivHom_fst, fst_add, fst_inl, fst_inr, add_zero, algebraMap_gaussX]
      · rw [dualMap_snd, invDerivHom_snd, snd_add, snd_inl, snd_inr, zero_add, invDeriv_genX,
          gaussDX]
        simp only [map_add (f := _), map_mul, map_ofNat, algebraMap_gaussX, algebraMap_gaussY,
          algebraMap_gauss_const]
        rfl
    · simp only [RingHom.comp_apply, gaussDual_algebraMap, gaussDualA_Y]
      rw [show algebraMap W.toAffine.CoordinateRing (gaussRing W) (CoordinateRing.mk W Y) =
        gaussY W from rfl, algebraMap_gaussY]
      ext
      · rw [dualMap_fst, invDerivHom_fst, fst_add, fst_inl, fst_inr, add_zero, algebraMap_gaussY]
      · rw [dualMap_snd, invDerivHom_snd, snd_add, snd_inl, snd_inr, zero_add, invDeriv_genY,
          gaussDY]
        simp only [map_add (f := _), map_sub, map_mul, map_pow, map_ofNat, algebraMap_gaussX,
          algebraMap_gaussY, algebraMap_gauss_const]
        rfl
  have := congrArg (fun f => (f g).snd) key
  simp only [RingHom.comp_apply, dualMap_snd, invDerivHom_snd] at this
  rw [gaussDeriv]
  exact this

theorem gaussResidue_gaussDeriv (g : gaussRing W) :
    gaussResidue W (residue _ (gaussDeriv K W g)) =
      invDeriv (W.map (residue 𝒪)) (gaussResidue W (residue _ g)) := by
  have key : (dualMap ((gaussResidue W).comp (residue (gaussRing W)))).comp (gaussDual K W) =
      (invDerivHom (W.map (residue 𝒪))).comp ((gaussResidue W).comp (residue (gaussRing W))) := by
    apply IsLocalization.ringHom_ext (gaussPrime W).primeCompl
    apply coordinateRing_ringHom_ext
    · intro c
      simp only [RingHom.comp_apply,
        ← IsScalarTower.algebraMap_apply 𝒪 W.toAffine.CoordinateRing (gaussRing W),
        gaussDual_algebraMap_base]
      ext
      · rw [dualMap_fst, invDerivHom_fst, fst_inl]; rfl
      · rw [dualMap_snd, invDerivHom_snd, snd_inl, map_zero,
          gaussResidue_residue_algebraMap, invDeriv_algebraMap]
    · simp only [RingHom.comp_apply, gaussDual_algebraMap, gaussDualA_X]
      rw [show algebraMap W.toAffine.CoordinateRing (gaussRing W) (CoordinateRing.mk W (C X)) =
        gaussX W from rfl]
      ext
      · rw [dualMap_fst, invDerivHom_fst, fst_add, fst_inl, fst_inr, add_zero]; rfl
      · rw [dualMap_snd, invDerivHom_snd, snd_add, snd_inl, snd_inr, zero_add, gaussResidue_gaussX, invDeriv_genX, gaussDX]
        simp only [map_add (f := _), map_mul, map_ofNat, RingHom.comp_apply, gaussResidue_gaussX,
          gaussResidue_gaussY, gaussResidue_residue_algebraMap]
        rfl
    · simp only [RingHom.comp_apply, gaussDual_algebraMap, gaussDualA_Y]
      rw [show algebraMap W.toAffine.CoordinateRing (gaussRing W) (CoordinateRing.mk W Y) =
        gaussY W from rfl]
      ext
      · rw [dualMap_fst, invDerivHom_fst, fst_add, fst_inl, fst_inr, add_zero]; rfl
      · rw [dualMap_snd, invDerivHom_snd, snd_add, snd_inl, snd_inr, zero_add, gaussResidue_gaussY, invDeriv_genY, gaussDY]
        simp only [map_add (f := _), map_sub, map_mul, map_pow, map_ofNat, RingHom.comp_apply,
          gaussResidue_gaussX, gaussResidue_gaussY, gaussResidue_residue_algebraMap]
        rfl
  have := congrArg (fun f => (f g).snd) key
  simp only [RingHom.comp_apply, dualMap_snd, invDerivHom_snd] at this
  rw [gaussDeriv]
  exact this

end Compat

section Isog

variable {𝒪 : Type u} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type u) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W W' : WeierstrassCurve 𝒪)
  [W.IsElliptic] [W'.IsElliptic] (φ : Isogeny (W.baseChange K) (W'.baseChange K))



theorem exists_invConst_reduceIsogeny :
    ∃ c : 𝒪, algebraMap 𝒪 K c = invConst φ ∧
      residue 𝒪 c = invConst (reduceIsogeny K W W' φ) := by
  obtain ⟨x, y, h, hφ⟩ := exists_isogeny_coords K W W' φ
  obtain ⟨h', hred⟩ := reduceFF_some K W W' h
  have hφ' : (reduceIsogeny K W W' φ).1 = Point.some _ _ h' := by
    rw [reduceIsogeny_val, hφ, hred]
  set u : gaussRing W := 2 * y + algebraMap 𝒪 _ W'.a₁ * x + algebraMap 𝒪 _ W'.a₃ with hu_def

  have hu_res : gaussResidue W (residue _ u) = 2 * gaussResidue W (residue _ y) +
      algebraMap (ResidueField 𝒪) _ (W'.map (residue 𝒪)).a₁ * gaussResidue W (residue _ x) +
        algebraMap (ResidueField 𝒪) _ (W'.map (residue 𝒪)).a₃ := by
    simp only [hu_def, map_add (f := _), map_mul, map_ofNat, gaussResidue_residue_algebraMap]
    rfl
  have hu_ne : gaussResidue W (residue _ u) ≠ 0 := by
    have hg := (reduceIsogeny K W W' φ).isGenPt
    rw [hφ'] at hg
    have hd := genDen_ne_zero (W'.map (residue 𝒪))
    intro h0
    apply hd
    apply (genEval (W'.map (residue 𝒪)) _ hg).toRingHom.injective
    rw [map_zero, ← h0, hu_res]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_add (f := _), map_mul, map_ofNat,
      AlgHom.commutes, genEval_genX, genEval_genY]
    rfl
  have hu : IsUnit u := by
    by_contra hnu
    exact hu_ne (by rw [(residue_eq_zero_iff _).2 ((mem_maximalIdeal _).2 hnu), map_zero])

  have e1 : isogCoeff φ * algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField u =
      algebraMap (gaussRing W) _ (gaussDeriv K W x) := by
    rw [algebraMap_gaussDeriv, ← isogCoeff_mul φ hφ]
    congr 1
    simp only [hu_def, map_add (f := _), map_mul, map_ofNat, algebraMap_gauss_const]
    rfl
  set v : gaussRing W := gaussDeriv K W x * ↑hu.unit⁻¹ with hv_def
  have hv : algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField v = isogCoeff φ := by
    have hne : algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField u ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hu.ne_zero
    rw [hv_def, map_mul, ← e1, mul_assoc, ← map_mul, IsUnit.mul_val_inv, map_one, mul_one]

  have hint : invConst φ ∈ Set.range (algebraMap 𝒪 K) := by
    by_contra hX
    obtain ⟨t, ht, hte⟩ := exists_inv_mem_of_notMem_range K hX
    have hc0 : invConst φ ≠ 0 := fun h0 => hX ⟨0, by rw [map_zero, h0]⟩
    have h1 : v * algebraMap 𝒪 (gaussRing W) t = 1 := by
      apply IsFractionRing.injective (gaussRing W) (W.baseChange K).toAffine.FunctionField
      rw [map_mul, hv, algebraMap_gauss_const, hte, ← algebraMap_invConst, map_inv₀,
        mul_inv_cancel₀ ((_root_.map_ne_zero _).2 hc0), map_one]
    have : IsUnit (algebraMap 𝒪 (gaussRing W) t) :=
      isUnit_iff_exists_inv.2 ⟨v, by rw [mul_comm]; exact h1⟩
    exact (mem_maximalIdeal _).1 ht ((isUnit_map_iff (algebraMap 𝒪 (gaussRing W)) t).1 this)
  obtain ⟨c, hc⟩ := hint
  refine ⟨c, hc, ?_⟩
  have hvc : algebraMap 𝒪 (gaussRing W) c = v := by
    apply IsFractionRing.injective (gaussRing W) (W.baseChange K).toAffine.FunctionField
    rw [algebraMap_gauss_const, hc, algebraMap_invConst, hv]

  have e2 := isogCoeff_mul (reduceIsogeny K W W' φ) hφ'
  rw [← gaussResidue_gaussDeriv K W x] at e2
  have e2' : isogCoeff (reduceIsogeny K W W' φ) = gaussResidue W (residue _ v) := by
    have hres_u : gaussResidue W (residue _ u) * gaussResidue W (residue _ ↑hu.unit⁻¹) = 1 := by
      rw [← map_mul, ← map_mul, IsUnit.mul_val_inv, map_one, map_one]
    rw [hv_def, map_mul, map_mul, ← e2, ← hu_res, mul_assoc, hres_u, mul_one]
  apply (algebraMap (ResidueField 𝒪) (W.map (residue 𝒪)).toAffine.FunctionField).injective
  rw [algebraMap_invConst, e2', ← hvc, gaussResidue_residue_algebraMap]

end Isog

end

end GroundTheory.Global
end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.GlobalFields.ComplexMultiplication.ReductionDifferential =====

-- ===== clump member: GroundTheory.GlobalFields.ComplexMultiplication.AlgebraicityDescent =====
-- clump-header: {"m": "GroundTheory.GlobalFields.ComplexMultiplication.AlgebraicityDescent", "h": "module\n\npublic import GroundTheory.GlobalFields.ComplexMultiplication.BaseChangeGalois\npublic import GroundTheory.GlobalFields.ComplexMultiplication.DifferentialConstantField\npublic import Mathlib.Basic.Complex.Basic\npublic import GroundTheory.GlobalFields.ComplexMultiplication.AlgebraicityHom\npublic import GroundTheory.GlobalFields.ComplexMultiplication.AutCFixed\npublic import GroundTheory.GlobalFields.ComplexMultiplication.BaseChangeDegree\nimport GroundTheory.GlobalFields.ComplexMultiplication.BaseChangeDescent\npublic import GroundTheory.GlobalFields.ComplexMultiplication.BaseChangeField\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\npublic import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex\n\n"}
section -- clump:auto
@[expose] public section

open NumberField Module WeierstrassCurve GroundTheory.Arith.Abelian IntermediateField Polynomial

noncomputable section

namespace GroundTheory.Global

section Descent

variable {L : Type} [Field L] [CharZero L] [Algebra L ℂ] {W W' : WeierstrassCurve L} [W.IsElliptic]
  [W'.IsElliptic]

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.exists_map_eq_of_forall_conj_eq
    (ψ : Isogeny (W.baseChange ℂ) (W'.baseChange ℂ)) (h : ∀ g : ℂ ≃ₐ[L] ℂ, ψ.conj g = ψ) :
    ∃ φ : Isogeny W W', φ.map (algebraMap L ℂ) = ψ := by
  classical
  have hxfix : ∀ g : ℂ ≃ₐ[L] ℂ, galFF W g ψ.x = ψ.x := fun g ↦ by rw [← Isogeny.conj_alt_bis, h g]
  have hyfix : ∀ g : ℂ ≃ₐ[L] ℂ, galFF W g ψ.y = ψ.y := fun g ↦ by rw [← Isogeny.conj_y, h g]
  obtain ⟨r, hr⟩ := ψ.exists_ratEmb_eq_x
  obtain ⟨a, b, ha, hb, hab⟩ := exists_eq_add_mul_genY (W.baseChange ℂ) ψ.y
  have ha' := ha
  have hb' := hb
  rw [← fieldRange_ratEmb] at ha' hb'
  obtain ⟨r₂, hr₂⟩ := ha'
  obtain ⟨r₃, hr₃⟩ := hb'
  change ratEmb (W.baseChange ℂ) r₂ = a at hr₂
  change ratEmb (W.baseChange ℂ) r₃ = b at hr₃
  have hab_fix : ∀ g : ℂ ≃ₐ[L] ℂ, galFF W g a = a ∧ galFF W g b = b := by
    intro g
    have e := hyfix g
    rw [hab, map_add (f := _), map_mul, galFF_genY] at e
    exact eq_of_add_mul_genY_eq (galFF_mem_adjoin_genX W _ ha) (galFF_mem_adjoin_genX W _ hb)
      ha hb e
  have hlift : ∀ s : RatFunc ℂ, (∀ g : ℂ ≃ₐ[L] ℂ,
      galFF W g (ratEmb (W.baseChange ℂ) s) = ratEmb (W.baseChange ℂ) s) →
      (∃ p : L[X], p.map (algebraMap L ℂ) = s.num) ∧
        ∃ q : L[X], q.map (algebraMap L ℂ) = s.denom := by
    intro s hs
    have hc : ∀ c ∈ s.num.coeffs ∪ s.denom.coeffs, c ∈ Set.range (algebraMap L ℂ) := by
      intro c hc
      have hbot : c ∈ (⊥ : IntermediateField L ℂ) := by
        refine (mem_bot_iff_forall_algEquiv_apply_eq (F := L)).2 fun g ↦ ?_
        obtain ⟨h1, h2⟩ := map_eq_of_galFF_ratEmb W g (hs g)
        rcases Finset.mem_union.mp hc with hc | hc
        · obtain ⟨n, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp hc
          have := congrArg (fun p : ℂ[X] ↦ p.coeff n) h1
          simpa using this
        · obtain ⟨n, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp hc
          have := congrArg (fun p : ℂ[X] ↦ p.coeff n) h2
          simpa using this
      exact IntermediateField.mem_bot.1 hbot
    constructor
    · rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
      intro n
      by_cases hn : s.num.coeff n = 0
      · exact ⟨0, by rw [hn, map_zero]⟩
      · exact hc _ (Finset.mem_union_left _ (coeff_mem_coeffs hn))
    · rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
      intro n
      by_cases hn : s.denom.coeff n = 0
      · exact ⟨0, by rw [hn, map_zero]⟩
      · exact hc _ (Finset.mem_union_right _ (coeff_mem_coeffs hn))
  obtain ⟨⟨n₁, hn₁⟩, ⟨d₁, hd₁⟩⟩ := hlift r (fun g ↦ by rw [hr]; exact hxfix g)
  obtain ⟨⟨n₂, hn₂⟩, ⟨d₂, hd₂⟩⟩ := hlift r₂ (fun g ↦ by rw [hr₂]; exact (hab_fix g).1)
  obtain ⟨⟨n₃, hn₃⟩, ⟨d₃, hd₃⟩⟩ := hlift r₃ (fun g ↦ by rw [hr₃]; exact (hab_fix g).2)
  set X₁ := genX W
  set x₁ : W.toAffine.FunctionField := aeval X₁ n₁ / aeval X₁ d₁
  set y₁ : W.toAffine.FunctionField :=
    aeval X₁ n₂ / aeval X₁ d₂ + aeval X₁ n₃ / aeval X₁ d₃ * genY W
  have hrat : ∀ (s : RatFunc ℂ) (p q : L[X]), p.map (algebraMap L ℂ) = s.num →
      q.map (algebraMap L ℂ) = s.denom →
      ffMap (algebraMap L ℂ) W (aeval X₁ p / aeval X₁ q) = ratEmb (W.baseChange ℂ) s := by
    intro s p q hp hq
    conv_rhs => rw [← RatFunc.num_div_denom s]
    rw [ratEmb_div, map_div₀, ffMap_aeval, ffMap_aeval, ffMap_genX, hp, hq]
    rfl
  have hx₁ : ffMap (algebraMap L ℂ) W x₁ = ψ.x := by
    rw [← hr]
    exact hrat r n₁ d₁ hn₁ hd₁
  have hy₁ : ffMap (algebraMap L ℂ) W y₁ = ψ.y := by
    rw [hab, map_add (f := _), map_mul, ← hr₂, ← hr₃, hrat r₂ n₂ d₂ hn₂ hd₂, hrat r₃ n₃ d₃ hn₃ hd₃,
      ffMap_genY]
    rfl
  exact ⟨Isogeny.ofMap (algebraMap L ℂ) ψ x₁ y₁ hx₁ hy₁,
    Isogeny.map_ofMap (algebraMap L ℂ) ψ x₁ y₁ hx₁ hy₁⟩

omit [CharZero L] [W.IsElliptic] [W'.IsElliptic] in
theorem _root_.GroundTheory.Arith.Abelian.Isogeny.invConst_congr {F : Type} [Field F]
    {C D C' D' : WeierstrassCurve F} [C.IsElliptic] [D.IsElliptic] [C'.IsElliptic]
    [D'.IsElliptic] (hC : C = D) (hC' : C' = D') (φ : Isogeny C C') :
    invConst (φ.congr hC hC') = invConst φ := by
  subst hC hC'
  rw [Isogeny.congr_rfl]


omit [CharZero L] in
theorem _root_.GroundTheory.Arith.Abelian.Isogeny.invConst_conj (g : ℂ ≃ₐ[L] ℂ)
    (ψ : Isogeny (W.baseChange ℂ) (W'.baseChange ℂ)) : invConst (ψ.conj g) = g (invConst ψ) := by
  rw [Isogeny.conj, Isogeny.mapOf, Isogeny.invConst_congr, invConst_map]
  rfl

end Descent

end GroundTheory.Global
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.GlobalFields.ComplexMultiplication.AlgebraicityDescent =====

-- ===== clump member: GroundTheory.GlobalFields.ComplexMultiplication.FrobeniusAtPrimesLocal =====
-- clump-header: {"m": "GroundTheory.GlobalFields.ComplexMultiplication.FrobeniusAtPrimesLocal", "h": "module\n\npublic import GroundTheory.GlobalFields.ComplexMultiplication.DifferentialConstantField\npublic import GroundTheory.GlobalFields.ComplexMultiplication.DualDescent\npublic import GroundTheory.GlobalFields.ComplexMultiplication.InseparableFrobenius\npublic import GroundTheory.GlobalFields.ComplexMultiplication.ReductionIsogenyMap\npublic import GroundTheory.GlobalFields.ComplexMultiplication.GoodReductionAlmostAll\npublic import GroundTheory.GlobalFields.ComplexMultiplication.InseparableFrobeniusFactor\npublic import GroundTheory.GlobalFields.ComplexMultiplication.IsogenyDegreeOne\npublic import GroundTheory.GlobalFields.ComplexMultiplication.ReductionDegree\npublic import GroundTheory.GlobalFields.ComplexMultiplication.ReductionDifferential\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace GroundTheory.Global

noncomputable section

open IsLocalRing GroundTheory.Arith.Abelian

universe u

variable {𝒪 : Type u} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (F : Type u) [Field F] [Algebra 𝒪 F] [IsFractionRing 𝒪 F] {W W' : WeierstrassCurve 𝒪}
  [W.IsElliptic] [W'.IsElliptic]

theorem invConst_reduceIsogeny_eq_zero (φ : Isogeny (W.baseChange F) (W'.baseChange F)) {c : 𝒪}
    (hc : c ∈ maximalIdeal 𝒪) (hφ : algebraMap 𝒪 F c = invConst φ) :
    invConst (reduceIsogeny F W W' φ) = 0 := by
  obtain ⟨c', h1, h2⟩ := exists_invConst_reduceIsogeny F W W' φ
  have e : c' = c := IsFractionRing.injective 𝒪 F (h1.trans hφ.symm)
  rw [← h2, e]
  exact (residue_eq_zero_iff c).2 hc

theorem isogenyPullback_reduceIsogeny_eq_zero (φ : Isogeny (W.baseChange F) (W'.baseChange F))
    {c : 𝒪} (hc : c ∈ maximalIdeal 𝒪) (hφ : algebraMap 𝒪 F c = invConst φ) :
    isogenyPullback (reduceIsogeny F W W' φ) (invariantDifferential (W'.map (residue 𝒪))) = 0 := by
  rw [isogenyPullback_eq_invConst_smul, invConst_reduceIsogeny_eq_zero F φ hc hφ, zero_smul]

variable (p : ℕ) [Fact p.Prime] [CharP (ResidueField 𝒪) p] [PerfectRing (ResidueField 𝒪) p]

theorem reduceIsogeny_eq_comp_frobeniusIsogeny (φ : Isogeny (W.baseChange F) (W'.baseChange F))
    (hdeg : φ.degree = p) {c : 𝒪} (hc : c ∈ maximalIdeal 𝒪) (hφ : algebraMap 𝒪 F c = invConst φ) :
    ∃ ψ : Isogeny (frobeniusTwist (W.map (residue 𝒪)) p) (W'.map (residue 𝒪)),
      reduceIsogeny F W W' φ = ψ.comp (frobeniusIsogeny (W.map (residue 𝒪)) p) ∧
      ψ.degree = 1 ∧ Function.Bijective ψ.comap ∧
      (dualOver ψ).comp ψ = mulIsogeny _ 1 one_ne_zero ∧
      ψ.comp (dualOver ψ) = mulIsogeny _ 1 one_ne_zero :=
  exists_isomorphism_of_degree_eq p _ (isogenyPullback_reduceIsogeny_eq_zero F φ hc hφ)
    (by rw [degree_reduceIsogeny, hdeg])

theorem residue_j_eq_pow (φ : Isogeny (W.baseChange F) (W'.baseChange F)) (hdeg : φ.degree = p)
    {c : 𝒪} (hc : c ∈ maximalIdeal 𝒪) (hφ : algebraMap 𝒪 F c = invConst φ) :
    residue 𝒪 W'.j = residue 𝒪 W.j ^ p := by
  rw [← j_map_residue, ← j_map_residue]
  exact j_eq_pow_of_isogenyPullback_eq_zero p _ (isogenyPullback_reduceIsogeny_eq_zero F φ hc hφ)
    (by rw [degree_reduceIsogeny, hdeg])

end

end GroundTheory.Global
end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.GlobalFields.ComplexMultiplication.FrobeniusAtPrimesLocal =====

-- ===== clump member: GroundTheory.GlobalFields.ComplexMultiplication.FrobeniusAtPrimes =====
-- clump-header: {"m": "GroundTheory.GlobalFields.ComplexMultiplication.FrobeniusAtPrimes", "h": "module\n\npublic import GroundTheory.GlobalFields.ComplexMultiplication.AlgebraicityGalois\npublic import GroundTheory.GlobalFields.ComplexMultiplication.DualDescent\npublic import GroundTheory.GlobalFields.ComplexMultiplication.InseparableFrobenius\npublic import GroundTheory.GlobalFields.ComplexMultiplication.PrimeLocalization\npublic import GroundTheory.GlobalFields.ComplexMultiplication.ReductionIsogenyMap\npublic import GroundTheory.GlobalFields.SemilocalAlgebras.Galois\npublic import GroundTheory.GlobalFields.TateThesis.DegreeOnePrimes\npublic import Mathlib.RingTheory.Frobenius\npublic import GroundTheory.GlobalFields.ComplexMultiplication.AlgebraicityDescent\npublic import GroundTheory.GlobalFields.ComplexMultiplication.BadPrimesFinite\nimport GroundTheory.GlobalFields.ComplexMultiplication.BaseChangeDescent\npublic import GroundTheory.GlobalFields.ComplexMultiplication.FrobeniusAtPrimesIsogeny\npublic import GroundTheory.GlobalFields.ComplexMultiplication.FrobeniusAtPrimesLocal\nimport GroundTheory.GlobalFields.ComplexMultiplication.GoodReductionAlmostAll\nimport GroundTheory.GlobalFields.ComplexMultiplication.JInvariantSurjective\nimport GroundTheory.GlobalFields.ComplexMultiplication.ReductionDifferential\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace GroundTheory.Global
namespace Elliptic

noncomputable section

open NumberField IsDedekindDomain IsLocalRing Module WeierstrassCurve GroundTheory.Arith.Abelian
open scoped nonZeroDivisors

section Residue

variable {L : Type*} [Field L] [NumberField L] (𝔓 : HeightOneSpectrum (𝓞 L))

instance finite_residueField_localizationAt : Finite (ResidueField (localizationAt L 𝔓)) :=
  Finite.of_equiv _
    (IsLocalization.AtPrime.equivQuotMaximalIdeal 𝔓.asIdeal (localizationAt L 𝔓)).toEquiv

theorem algebraMap_mem_maximalIdeal_localizationAt_iff (a : 𝓞 L) :
    algebraMap (𝓞 L) (localizationAt L 𝔓) a ∈ maximalIdeal (localizationAt L 𝔓) ↔ a ∈ 𝔓.asIdeal :=
  IsLocalization.AtPrime.to_map_mem_maximal_iff _ _ a

theorem charP_residueField_localizationAt {p : ℕ} (hp : p.Prime) (hmem : (p : 𝓞 L) ∈ 𝔓.asIdeal) :
    CharP (ResidueField (localizationAt L 𝔓)) p := by
  rw [CharP.charP_iff_prime_eq_zero hp]
  have h := (algebraMap_mem_maximalIdeal_localizationAt_iff 𝔓 p).2 hmem
  rw [map_natCast] at h
  rw [← map_natCast (IsLocalRing.residue (localizationAt L 𝔓)), residue_eq_zero_iff]
  exact h

variable {K : Type*} [Field K] [Algebra K L]

theorem residue_smul_of_isArithFrobAt {σ : L ≃ₐ[K] L} (hσ : IsArithFrobAt (𝓞 K) σ 𝔓.asIdeal)
    (a : 𝓞 L) :
    IsLocalRing.residue (localizationAt L 𝔓) (algebraMap (𝓞 L) _ (σ • a)) =
      IsLocalRing.residue (localizationAt L 𝔓) (algebraMap (𝓞 L) _ a) ^
        Nat.card (𝓞 K ⧸ 𝔓.asIdeal.under (𝓞 K)) := by
  rw [← sub_eq_zero, ← map_pow, ← map_sub, residue_eq_zero_iff, ← map_pow, ← map_sub,
    algebraMap_mem_maximalIdeal_localizationAt_iff]
  exact hσ a


omit [NumberField L] in
theorem smul_notMem_of_isArithFrobAt {σ : L ≃ₐ[K] L} (hσ : IsArithFrobAt (𝓞 K) σ 𝔓.asIdeal)
    {s : 𝓞 L} (hs : s ∉ 𝔓.asIdeal) : σ • s ∉ 𝔓.asIdeal := by
  intro h
  apply hs
  have h' : s ^ Nat.card (𝓞 K ⧸ 𝔓.asIdeal.under (𝓞 K)) ∈ 𝔓.asIdeal := by
    have := 𝔓.asIdeal.sub_mem h (hσ s)
    simpa using this
  exact 𝔓.isPrime.mem_of_pow_mem _ h'

theorem residue_apply_of_isArithFrobAt {σ : L ≃ₐ[K] L} (hσ : IsArithFrobAt (𝓞 K) σ 𝔓.asIdeal)
    {x : L} (hx : x ∈ localizationAt L 𝔓) :
    ∃ h : σ x ∈ localizationAt L 𝔓, IsLocalRing.residue (localizationAt L 𝔓) ⟨σ x, h⟩ =
      IsLocalRing.residue (localizationAt L 𝔓) ⟨x, hx⟩ ^ Nat.card (𝓞 K ⧸ 𝔓.asIdeal.under (𝓞 K)) := by
  set q := Nat.card (𝓞 K ⧸ 𝔓.asIdeal.under (𝓞 K))
  obtain ⟨a, s, hs, hxs⟩ := mem_localizationAt_iff.1 hx
  have hs0 : (algebraMap (𝓞 L) L s) ≠ 0 := by
    intro h0
    apply hs
    rw [(IsFractionRing.injective (𝓞 L) L) (h0.trans (map_zero _).symm)]
    exact 𝔓.asIdeal.zero_mem
  have hσs := smul_notMem_of_isArithFrobAt 𝔓 hσ hs
  have hσs0 : (algebraMap (𝓞 L) L (σ • s)) ≠ 0 := by
    intro h0
    apply hσs
    rw [(IsFractionRing.injective (𝓞 L) L) (h0.trans (map_zero _).symm)]
    exact 𝔓.asIdeal.zero_mem
  have hσx : σ x = algebraMap (𝓞 L) L (σ • a) * (algebraMap (𝓞 L) L (σ • s))⁻¹ := by
    rw [hxs, map_mul, map_inv₀]
    rfl
  have hmem : σ x ∈ localizationAt L 𝔓 := mem_localizationAt_iff.2 ⟨σ • a, σ • s, hσs, hσx⟩
  refine ⟨hmem, ?_⟩
  set R := localizationAt L 𝔓
  set A := algebraMap (𝓞 L) R
  have e1 : (⟨x, hx⟩ : R) * A s = A a := by
    apply Subtype.ext
    change x * algebraMap (𝓞 L) L s = algebraMap (𝓞 L) L a
    rw [hxs, mul_assoc, inv_mul_cancel₀ hs0, mul_one]
  have e2 : (⟨σ x, hmem⟩ : R) * A (σ • s) = A (σ • a) := by
    apply Subtype.ext
    change σ x * algebraMap (𝓞 L) L (σ • s) = algebraMap (𝓞 L) L (σ • a)
    rw [hσx, mul_assoc, inv_mul_cancel₀ hσs0, mul_one]
  have hres : IsLocalRing.residue R (A (σ • s)) ≠ 0 := by
    rw [Ne, residue_eq_zero_iff, algebraMap_mem_maximalIdeal_localizationAt_iff]
    exact hσs
  have r1 := congrArg (IsLocalRing.residue R) e1
  have r2 := congrArg (IsLocalRing.residue R) e2
  rw [map_mul] at r1 r2
  rw [residue_smul_of_isArithFrobAt 𝔓 hσ, residue_smul_of_isArithFrobAt 𝔓 hσ, ← r1, mul_pow] at r2
  exact mul_right_cancel₀ (by rwa [residue_smul_of_isArithFrobAt 𝔓 hσ] at hres) r2

end Residue

section DegreeOne

theorem intCast_surjective_ringOfIntegers_rat :
    Function.Surjective (Int.castRingHom (𝓞 ℚ)) := by
  intro z
  refine ⟨Rat.ringOfIntegersEquiv z, Rat.ringOfIntegersEquiv.injective ?_⟩
  simp

theorem absNorm_prime_of_ringOfIntegers_rat (𝔮 : Ideal (𝓞 ℚ)) (h0 : 𝔮 ≠ ⊥) [𝔮.IsMaximal] :
    (Ideal.absNorm 𝔮).Prime := by
  let _ : Field (𝓞 ℚ ⧸ 𝔮) := Ideal.Quotient.field 𝔮
  have hfin : Finite (𝓞 ℚ ⧸ 𝔮) := Ideal.finiteQuotientOfFreeOfNeBot 𝔮 h0
  set p := ringChar (𝓞 ℚ ⧸ 𝔮)
  have hp : p.Prime := (CharP.char_is_prime_or_zero (𝓞 ℚ ⧸ 𝔮) p).resolve_right
    (CharP.char_ne_zero_of_finite (𝓞 ℚ ⧸ 𝔮) p)
  have : Fact p.Prime := ⟨hp⟩
  let f : ZMod p →+* 𝓞 ℚ ⧸ 𝔮 := ZMod.castHom (dvd_refl p) _
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨n, rfl⟩ := intCast_surjective_ringOfIntegers_rat z
    exact ⟨n, by simp [f]⟩
  have hbij : Function.Bijective f := ⟨f.injective, hsurj⟩
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, ← Nat.card_congr (Equiv.ofBijective f hbij),
    Nat.card_zmod]
  exact hp

theorem absNorm_prime_of_mem_degreeOnePrimes {K : Type*} [Field K] [NumberField K]
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ degreeOnePrimes ℚ K) :
    (Ideal.absNorm v.asIdeal).Prime := by
  have h := Ideal.absNorm_pow_inertiaDeg (v.asIdeal.under (𝓞 ℚ)) v.asIdeal
  have hv' : v.asIdeal.inertiaDeg (𝓞 ℚ) = 1 := hv
  rw [hv', pow_one] at h
  rw [← h]
  have hne : v.asIdeal.under (𝓞 ℚ) ≠ ⊥ := by
    intro hb
    exact v.ne_bot (Ideal.eq_bot_of_under_eq_bot hb)
  have : (v.asIdeal.under (𝓞 ℚ)).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hne
  exact absNorm_prime_of_ringOfIntegers_rat _ hne

end DegreeOne

section LatticeForm

variable {K : Type*} [Field K] [NumberField K] (σ₀ : K →+* ℂ) (hK : finrank ℚ K = 2)
  [_root_.NumberField.IsTotallyComplex K]

include hK in
theorem exists_unit_of_homConstSet_eq (L L' : PeriodPair) (hL : periodLatticeEnd L = cmRingOfEmbedding σ₀)
    (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (hL' : L'.lattice = idealLattice σ₀ ↑𝔞⁻¹ * L.lattice)
    (φ : Isogeny (weierstrassCurve L) (weierstrassCurve L'))
    (hφ : (homConstSet (weierstrassCurve L) (weierstrassCurve L') : Set ℂ) =
      (invConst φ * ·) '' idealLattice σ₀ ↑𝔞⁻¹) :
    ∃ u : (𝓞 K)ˣ, invConst φ = σ₀ (algebraMap (𝓞 K) K u) ∧
      ∀ z : ℂ, homPt φ.toHom (toPoint L z) = toPoint L' (σ₀ (algebraMap (𝓞 K) K u) * z) := by
  classical
  set c := invConst φ with hcdef
  have hc : c ≠ 0 := invConst_ne_zero φ
  have hM : (idealLattice σ₀ ↑𝔞⁻¹ : Set ℂ) = (c * ·) '' idealLattice σ₀ ↑𝔞⁻¹ := by
    rw [← hφ, homConstSet_weierstrassCurve, latticeHom_eq_idealLattice σ₀ hK L L' hL 𝔞⁻¹ hL']
  have hM' := eq_image_mul_inv hc hM
  have hP : (idealPeriodPair σ₀ hK 𝔞⁻¹).lattice = idealLattice σ₀ ↑𝔞⁻¹ :=
    lattice_idealPeriodPair σ₀ hK _
  have hPend : periodLatticeEnd (idealPeriodPair σ₀ hK 𝔞⁻¹) = cmRingOfEmbedding σ₀ := latticeEnd_idealPeriodPair σ₀ hK _
  have mult : ∀ d : ℂ, (idealLattice σ₀ ↑𝔞⁻¹ : Set ℂ) = (d * ·) '' idealLattice σ₀ ↑𝔞⁻¹ →
      d ∈ cmRingOfEmbedding σ₀ := by
    intro d hd
    rw [← hPend]
    intro l hl
    rw [hP] at hl ⊢
    have h' : d * l ∈ (idealLattice σ₀ ↑𝔞⁻¹ : Set ℂ) := by
      rw [hd]
      exact ⟨l, hl, rfl⟩
    exact h'
  obtain ⟨a, ha⟩ := (mem_cmRing σ₀).1 (mult c hM)
  obtain ⟨b, hb⟩ := (mem_cmRing σ₀).1 (mult c⁻¹ hM')
  have hinj : Function.Injective (σ₀.comp (algebraMap (𝓞 K) K)) :=
    σ₀.injective.comp (IsFractionRing.injective (𝓞 K) K)
  have hab : a * b = 1 := hinj (by
    simp only [RingHom.comp_apply, map_mul, map_one]
    rw [ha, hb, mul_inv_cancel₀ hc])
  refine ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ha.symm, fun z ↦ ?_⟩
  rw [← latticeToHom_homConst φ.toHom, homPt_latticeToHom]
  congr 1
  change homConst _ _ φ.toHom * z = _
  rw [homConst_toHom, ← hcdef, ← ha]

end LatticeForm

section Main

variable {K : Type*} [Field K] [NumberField K] [Algebra K ℂ] (hK : finrank ℚ K = 2)
  [_root_.NumberField.IsTotallyComplex K] {L : IntermediateField K ℂ} [NumberField L]


omit [NumberField K] [_root_.NumberField.IsTotallyComplex K] [NumberField L] in
theorem algebraMap_mem_of_liesOver {𝔭 : HeightOneSpectrum (𝓞 K)} {𝔓 : HeightOneSpectrum (𝓞 L)}
    [h : 𝔓.asIdeal.LiesOver 𝔭.asIdeal] {a : 𝓞 K} (ha : a ∈ 𝔭.asIdeal) :
    algebraMap (𝓞 K) (𝓞 L) a ∈ 𝔓.asIdeal := by
  rw [h.over] at ha
  exact ha


omit [NumberField K] [_root_.NumberField.IsTotallyComplex K] [NumberField L] in
theorem isogBaseChange_eq_map {A A' : WeierstrassCurve L} [A.IsElliptic] [A'.IsElliptic]
    (φ : Isogeny A A') : isogBaseChange (F' := ℂ) φ = φ.map (algebraMap L ℂ) :=
  Isogeny.ext_xy
    (by rw [isogBaseChange_alt, ← ffMap_algebraMap_eq_bcEmb]; exact (Isogeny.map_x _ φ).symm)
    (by rw [isogBaseChange_y, ← ffMap_algebraMap_eq_bcEmb]; exact (Isogeny.map_y _ φ).symm)


omit [NumberField L] in
include hK in
theorem exists_isogBaseChange_eq_of_isogeny {A A' : WeierstrassCurve L} [A.IsElliptic]
    [A'.IsElliptic] (hA : Nonempty (isogEnd (A.baseChange ℂ) ≃+* 𝓞 K)) (φ : Isogeny A A')
    (ψ : Isogeny (A.baseChange ℂ) (A'.baseChange ℂ)) :
    ∃ φ' : Isogeny A A', isogBaseChange φ' = ψ := by
  classical
  suffices h : ∀ g : ℂ ≃ₐ[L] ℂ, ψ.conj g = ψ by
    obtain ⟨φ', hφ'⟩ := ψ.exists_map_eq_of_forall_conj_eq h
    exact ⟨φ', (isogBaseChange_eq_map φ').trans hφ'⟩
  intro g
  set D := dualOver (isogBaseChange (F' := ℂ) φ)
  obtain ⟨Λ, C, hC⟩ := exists_variableChange_eq_weierstrassCurve (A.baseChange ℂ)
  have hΛ : _root_.periodLatticeEnd Λ = cmRingOfEmbedding (algebraMap K ℂ) :=
    latticeEnd_eq_cmRing_of_ringEquiv (algebraMap K ℂ) hK Λ
      ((latticeEndEquiv Λ).trans ((vcEndEquiv C hC).symm.trans hA.some))
  have hmem : endConst (A.baseChange ℂ) (D.comp ψ).toHom ∈ cmRingOfEmbedding (algebraMap K ℂ) := by
    rw [← hΛ, ← range_endConst hC]
    exact ⟨_, rfl⟩
  obtain ⟨a, ha⟩ := (mem_cmRing (algebraMap K ℂ)).1 hmem
  rw [endConst_apply, homConst_toHom, invConst_comp] at ha
  have hD := invConst_dualOver_mul (isogBaseChange (F' := ℂ) φ)
  rw [invConst_isogBaseChange, degree_isogBaseChange] at hD
  change invConst D * _ = _ at hD
  have hD0 : invConst D ≠ 0 := invConst_ne_zero D
  have hc0 : algebraMap L ℂ (invConst φ) ≠ 0 := by
    rw [← invConst_isogBaseChange]
    exact invConst_ne_zero _
  have hψ : invConst ψ = algebraMap L ℂ (algebraMap K L (algebraMap (𝓞 K) K a) * invConst φ /
      φ.degree) := by
    have hdeg0 : (φ.degree : ℂ) ≠ 0 := Nat.cast_ne_zero.2 φ.degree_pos.ne'
    rw [map_div₀, map_mul, map_natCast, ← IsScalarTower.algebraMap_apply, ha, ← hD]
    field_simp
  have hc : invConst (ψ.conj g) = invConst ψ := by
    rw [Isogeny.invConst_conj, hψ]
    exact g.commutes _
  have hQ : (ψ.conj g).toHom - ψ.toHom = 0 := by
    by_contra hne
    have h0 := invConst_ne_zero (isogOfHom _ hne)
    rw [← homConst_toHom, isogOfHom_toHom, map_sub, homConst_toHom, homConst_toHom, hc,
      sub_self] at h0
    exact h0 rfl
  have hQ' : (ψ.conj g).toHom = ψ.toHom := sub_eq_zero.1 hQ
  have h2 := congrArg Subtype.val hQ'
  exact Isogeny.ext' h2


include hK in
theorem exists_mem_maximalIdeal_invConst (𝔭 : HeightOneSpectrum (𝓞 K))
    (𝔓 : HeightOneSpectrum (𝓞 L)) [𝔓.asIdeal.LiesOver 𝔭.asIdeal]
    {W W' : WeierstrassCurve (localizationAt L 𝔓)} [W.IsElliptic] [W'.IsElliptic]
    (hEW : Nonempty (isogEnd ((W.baseChange L).baseChange ℂ) ≃+* 𝓞 K))
    (φ : Isogeny (W.baseChange L) (W'.baseChange L))
    (hφ : (homConstSet ((W.baseChange L).baseChange ℂ) ((W'.baseChange L).baseChange ℂ) : Set ℂ) =
      (algebraMap L ℂ (invConst φ) * ·) ''
        idealLattice (algebraMap K ℂ) (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹) :
    ∃ c ∈ maximalIdeal (localizationAt L 𝔓), algebraMap (localizationAt L 𝔓) L c = invConst φ := by
  classical
  set c := invConst φ with hcdef
  have hc0 : algebraMap L ℂ c ≠ 0 := by
    rw [hcdef, ← invConst_isogBaseChange]
    exact invConst_ne_zero _

  have step1 : ∀ β ∈ (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹,
      c * algebraMap K L β ∈ localizationAt L 𝔓 := by
    intro β hβ
    by_cases hβ0 : β = 0
    · rw [hβ0, map_zero, mul_zero]
      exact zero_mem _
    have hmem : algebraMap L ℂ c * algebraMap K ℂ β ∈
        homConstSet ((W.baseChange L).baseChange ℂ) ((W'.baseChange L).baseChange ℂ) := by
      have h' : algebraMap L ℂ c * algebraMap K ℂ β ∈ (homConstSet ((W.baseChange L).baseChange ℂ)
          ((W'.baseChange L).baseChange ℂ) : Set ℂ) := by
        rw [hφ]
        exact ⟨_, map_mem_idealLattice _ hβ, rfl⟩
      exact h'
    obtain ⟨Q, hQ⟩ := mem_homConstSet.1 hmem
    have hQ0 : Q ≠ 0 := by
      rintro rfl
      rw [map_zero] at hQ
      exact mul_ne_zero hc0 ((map_ne_zero _).2 hβ0) hQ.symm
    obtain ⟨ν, hν⟩ := exists_isogBaseChange_eq_of_isogeny hK hEW φ (isogOfHom Q hQ0)
    have e : algebraMap L ℂ (invConst ν) = algebraMap L ℂ (c * algebraMap K L β) := by
      rw [← invConst_isogBaseChange, hν, ← homConst_toHom, isogOfHom_toHom, hQ, map_mul,
        ← IsScalarTower.algebraMap_apply]
    have e' := (algebraMap L ℂ).injective e
    obtain ⟨d, hd, -⟩ := exists_invConst_reduceIsogeny L W W' ν
    rw [← e', ← hd]
    exact d.2

  have h1 : (1 : K) ∈ (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹ * (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [inv_mul_cancel₀ (FractionalIdeal.coeIdeal_ne_zero.2 𝔭.ne_bot)]
    exact FractionalIdeal.one_mem_one _
  have key := FractionalIdeal.mul_induction_on
    (C := fun z : K ↦ ∃ m ∈ maximalIdeal (localizationAt L 𝔓),
      algebraMap (localizationAt L 𝔓) L m = c * algebraMap K L z) h1
    (fun i hi j hj ↦ by
      obtain ⟨a, ha, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hj
      refine ⟨⟨c * algebraMap K L i, step1 i hi⟩ * algebraMap (𝓞 L) (localizationAt L 𝔓)
        (algebraMap (𝓞 K) (𝓞 L) a), Ideal.mul_mem_left _ _
          ((algebraMap_mem_maximalIdeal_localizationAt_iff 𝔓 _).2
            (algebraMap_mem_of_liesOver ha)), ?_⟩
      change c * algebraMap K L i * algebraMap (𝓞 L) L (algebraMap (𝓞 K) (𝓞 L) a) = _
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 K) K L, map_mul,
        mul_assoc])
    (fun x y ⟨m₁, hm₁, e₁⟩ ⟨m₂, hm₂, e₂⟩ ↦
      ⟨m₁ + m₂, add_mem hm₁ hm₂, by rw [map_add (f := _), e₁, e₂, map_add (f := _), mul_add]⟩)
  obtain ⟨m, hm, e⟩ := key
  exact ⟨m, hm, by rw [e, map_one, mul_one]⟩


include hK in
theorem reduceIsogeny_eq_comp_frobeniusIsogeny_of_homConstSet (𝔭 : HeightOneSpectrum (𝓞 K))
    (hv : (Ideal.absNorm 𝔭.asIdeal).Prime) (𝔓 : HeightOneSpectrum (𝓞 L))
    [𝔓.asIdeal.LiesOver 𝔭.asIdeal]
    {W W' : WeierstrassCurve (localizationAt L 𝔓)} [W.IsElliptic] [W'.IsElliptic]
    (hEW : Nonempty (isogEnd ((W.baseChange L).baseChange ℂ) ≃+* 𝓞 K))
    (hEW' : Nonempty (isogEnd ((W'.baseChange L).baseChange ℂ) ≃+* 𝓞 K))
    (φ : Isogeny (W.baseChange L) (W'.baseChange L))
    (hφ : (homConstSet ((W.baseChange L).baseChange ℂ) ((W'.baseChange L).baseChange ℂ) : Set ℂ) =
      (algebraMap L ℂ (invConst φ) * ·) ''
        idealLattice (algebraMap K ℂ) (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹)
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField (localizationAt L 𝔓)) p] :
    p = Ideal.absNorm 𝔭.asIdeal ∧ φ.degree = p ∧
      (∃ ψ : Isogeny (frobeniusTwist (W.map (IsLocalRing.residue _)) p)
          (W'.map (IsLocalRing.residue _)),
        reduceIsogeny L W W' φ = ψ.comp (frobeniusIsogeny (W.map (IsLocalRing.residue _)) p) ∧
        ψ.degree = 1 ∧ (dualOver ψ).comp ψ = mulIsogeny _ 1 one_ne_zero ∧
        ψ.comp (dualOver ψ) = mulIsogeny _ 1 one_ne_zero) ∧
      IsLocalRing.residue _ W'.j = IsLocalRing.residue _ W.j ^ p := by
  classical
  obtain ⟨c, hc, hcφ⟩ := exists_mem_maximalIdeal_invConst hK 𝔭 𝔓 hEW φ hφ
  have hdeg : φ.degree = Ideal.absNorm 𝔭.asIdeal := by
    have h := degree_eq_absNorm (algebraMap K ℂ) hK (E := ⟨_, hEW⟩) (E' := ⟨_, hEW'⟩) 𝔭 hv
      (isogBaseChange φ) (by rw [invConst_isogBaseChange]; exact hφ)
    rwa [degree_isogBaseChange] at h
  have hp : p = Ideal.absNorm 𝔭.asIdeal := by
    have hmem : ((Ideal.absNorm 𝔭.asIdeal : ℕ) : 𝓞 L) ∈ 𝔓.asIdeal := by
      have := algebraMap_mem_of_liesOver (𝔓 := 𝔓) (Ideal.absNorm_mem 𝔭.asIdeal)
      rwa [map_natCast] at this
    have h0 : ((Ideal.absNorm 𝔭.asIdeal : ℕ) : ResidueField (localizationAt L 𝔓)) = 0 := by
      have h := (algebraMap_mem_maximalIdeal_localizationAt_iff 𝔓 _).2 hmem
      rw [map_natCast] at h
      rw [← map_natCast (IsLocalRing.residue (localizationAt L 𝔓)), residue_eq_zero_iff]
      exact h
    have hdvd := (CharP.cast_eq_zero_iff (ResidueField (localizationAt L 𝔓)) p _).1 h0
    exact (Nat.prime_dvd_prime_iff_eq (Fact.out) hv).1 hdvd
  have hdeg' : φ.degree = p := hdeg.trans hp.symm
  obtain ⟨ψ, h1, h2, -, h4, h5⟩ := reduceIsogeny_eq_comp_frobeniusIsogeny L p φ hdeg' hc hcφ
  exact ⟨hp, hdeg', ⟨ψ, h1, h2, h4, h5⟩, residue_j_eq_pow L p φ hdeg' hc hcφ⟩


include hK in
theorem reduceIsogeny_congr_eq_comp_frobeniusIsogeny (𝔭 : HeightOneSpectrum (𝓞 K))
    (hv : (Ideal.absNorm 𝔭.asIdeal).Prime) (𝔓 : HeightOneSpectrum (𝓞 L))
    [𝔓.asIdeal.LiesOver 𝔭.asIdeal] {A A' : WeierstrassCurve L} [A.IsElliptic] [A'.IsElliptic]
    (hEA : Nonempty (isogEnd (A.baseChange ℂ) ≃+* 𝓞 K))
    (hEA' : Nonempty (isogEnd (A'.baseChange ℂ) ≃+* 𝓞 K))
    (φ : Isogeny A A')
    (hφ : (homConstSet (A.baseChange ℂ) (A'.baseChange ℂ) : Set ℂ) =
      (algebraMap L ℂ (invConst φ) * ·) ''
        idealLattice (algebraMap K ℂ) (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹)
    {W W' : WeierstrassCurve (localizationAt L 𝔓)} [W.IsElliptic] [W'.IsElliptic]
    (hW : W.map (algebraMap (localizationAt L 𝔓) L) = A)
    (hW' : W'.map (algebraMap (localizationAt L 𝔓) L) = A')
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField (localizationAt L 𝔓)) p] :
    p = Ideal.absNorm 𝔭.asIdeal ∧ φ.degree = p ∧
      (∃ ψ : Isogeny (frobeniusTwist (W.map (IsLocalRing.residue _)) p)
          (W'.map (IsLocalRing.residue _)),
        reduceIsogeny L W W' (φ.congr hW.symm hW'.symm) =
          ψ.comp (frobeniusIsogeny (W.map (IsLocalRing.residue _)) p) ∧
        ψ.degree = 1 ∧ (dualOver ψ).comp ψ = mulIsogeny _ 1 one_ne_zero ∧
        ψ.comp (dualOver ψ) = mulIsogeny _ 1 one_ne_zero) ∧
      IsLocalRing.residue _ W'.j = IsLocalRing.residue _ W.j ^ p := by
  subst hW hW'
  erw [Isogeny.congr_rfl]
  exact reduceIsogeny_eq_comp_frobeniusIsogeny_of_homConstSet hK 𝔭 hv 𝔓 hEA hEA' φ hφ p

end Main

section Global

variable {K : Type*} [Field K] [NumberField K] [Algebra K ℂ] (hK : finrank ℚ K = 2)
  [_root_.NumberField.IsTotallyComplex K] {L : IntermediateField K ℂ} [NumberField L]

abbrev primeClass (𝔭 : HeightOneSpectrum (𝓞 K)) : ClassGroup (𝓞 K) :=
  ClassGroup.mk0 ⟨𝔭.asIdeal, mem_nonZeroDivisors_of_ne_zero 𝔭.ne_bot⟩


omit [NumberField K] [_root_.NumberField.IsTotallyComplex K] [NumberField L] in
theorem ELL.j_eq_algebraMap_j {A : WeierstrassCurve L} [A.IsElliptic] {x : ELL K}
    {h : Nonempty (isogEnd (A.baseChange ℂ) ≃+* 𝓞 K)}
    (hx : (⟨A.baseChange ℂ, h⟩ : CMCurve K).toEll = x) : ELL.j x = algebraMap L ℂ A.j := by
  rw [← hx, ELL.j_toEll]
  exact WeierstrassCurve.map_j _ _


omit [NumberField L] in
include hK in
theorem exists_isogeny_primeClass_smul
    (E : ELL K → WeierstrassCurve L) [∀ x, (E x).IsElliptic]
    (hE : ∀ x, ∃ h : Nonempty (isogEnd ((E x).baseChange ℂ) ≃+* 𝓞 K),
      (⟨(E x).baseChange ℂ, h⟩ : CMCurve K).toEll = x)
    (hiso : ∀ x y, Nonempty (Isogeny (E x) (E y)))
    (𝔭 : HeightOneSpectrum (𝓞 K)) (x : ELL K) :
    ∃ φ : Isogeny (E x) (E ((ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x)),
      (homConstSet ((E x).baseChange ℂ)
          ((E ((ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x)).baseChange ℂ) : Set ℂ) =
        (algebraMap L ℂ (invConst φ) * ·) ''
          idealLattice (algebraMap K ℂ) (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹ ∧
      ((Ideal.absNorm 𝔭.asIdeal).Prime → φ.degree = Ideal.absNorm 𝔭.asIdeal) := by
  classical
  set y := (ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x
  obtain ⟨h₀, hx⟩ := hE x
  obtain ⟨h₁, hy⟩ := hE y
  obtain ⟨ψ, hψ⟩ := exists_isogeny_homConstSet_eq (algebraMap K ℂ) hK
    (E := ⟨_, h₀⟩) (E' := ⟨_, h₁⟩) 𝔭 (by rw [hx, hy])
  obtain ⟨φ, hφ⟩ := exists_isogBaseChange_eq_of_isogeny hK h₀ (hiso x y).some ψ
  have hφ' : (homConstSet ((E x).baseChange ℂ) ((E y).baseChange ℂ) : Set ℂ) =
      (algebraMap L ℂ (invConst φ) * ·) ''
        idealLattice (algebraMap K ℂ) (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
    rw [← invConst_isogBaseChange, hφ]
    exact hψ
  refine ⟨φ, hφ', fun hv ↦ ?_⟩
  have h := degree_eq_absNorm (algebraMap K ℂ) hK (E := ⟨_, h₀⟩) (E' := ⟨_, h₁⟩) 𝔭 hv
    (isogBaseChange φ) (by rw [invConst_isogBaseChange]; exact hφ')
  rwa [degree_isogBaseChange] at h


include hK in
theorem frobenius_at_primes_of_degree_one (hL : ∀ x : ELL K, ELL.j x ∈ L)
    (E : ELL K → WeierstrassCurve L) [∀ x, (E x).IsElliptic]
    (hE : ∀ x, ∃ h : Nonempty (isogEnd ((E x).baseChange ℂ) ≃+* 𝓞 K),
      (⟨(E x).baseChange ℂ, h⟩ : CMCurve K).toEll = x)
    (hiso : ∀ x y, Nonempty (Isogeny (E x) (E y))) :
    ∃ S : Set (HeightOneSpectrum (𝓞 K)), S.Finite ∧ ∀ 𝔭 ∉ S, 𝔭 ∈ degreeOnePrimes ℚ K →
      ∀ (𝔓 : HeightOneSpectrum (𝓞 L)) [𝔓.asIdeal.LiesOver 𝔭.asIdeal],
        (∃ (W : ELL K → WeierstrassCurve (localizationAt L 𝔓)) (_ : ∀ x, (W x).IsElliptic),
          (∀ x, (W x).map (algebraMap (localizationAt L 𝔓) L) = E x) ∧
          Pairwise fun x y ↦ IsLocalRing.residue _ (W x).j ≠ IsLocalRing.residue _ (W y).j) ∧
        (∀ σ : L ≃ₐ[K] L, IsArithFrobAt (𝓞 K) σ 𝔓.asIdeal →
          galClassOf hK L hL σ = primeClass 𝔭 ∧
          ∀ x : ELL K, σ ⟨ELL.j x, hL x⟩ =
            ⟨ELL.j ((ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x), hL _⟩) ∧
        ∀ (x : ELL K)
          (φ : Isogeny (E x) (E ((ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x))),
          (homConstSet ((E x).baseChange ℂ)
              ((E ((ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x)).baseChange ℂ) :
                Set ℂ) =
            (algebraMap L ℂ (invConst φ) * ·) ''
              idealLattice (algebraMap K ℂ) (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹ →
          ∀ (W W' : WeierstrassCurve (localizationAt L 𝔓)) [W.IsElliptic] [W'.IsElliptic]
            (hW : W.map (algebraMap (localizationAt L 𝔓) L) = E x)
            (hW' : W'.map (algebraMap (localizationAt L 𝔓) L) =
              E ((ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x))
            (p : ℕ) [Fact p.Prime] [CharP (ResidueField (localizationAt L 𝔓)) p],
            p = Ideal.absNorm 𝔭.asIdeal ∧ φ.degree = p ∧
              (∃ ψ : Isogeny (frobeniusTwist (W.map (IsLocalRing.residue _)) p)
                  (W'.map (IsLocalRing.residue _)),
                reduceIsogeny L W W' (φ.congr hW.symm hW'.symm) =
                  ψ.comp (frobeniusIsogeny (W.map (IsLocalRing.residue _)) p) ∧
                ψ.degree = 1 ∧ (dualOver ψ).comp ψ = mulIsogeny _ 1 one_ne_zero ∧
                ψ.comp (dualOver ψ) = mulIsogeny _ 1 one_ne_zero) ∧
              IsLocalRing.residue _ W'.j = IsLocalRing.residue _ W.j ^ p := by
  classical
  have : Finite (ELL K) := finite_ell hK
  have hj : ∀ x, ELL.j x = algebraMap L ℂ (E x).j := fun x ↦ by
    obtain ⟨h, hx⟩ := hE x
    exact ELL.j_eq_algebraMap_j hx
  have hEj : Pairwise fun x y ↦ (E x).j ≠ (E y).j := fun x y hxy e ↦
    hxy (ELL.j_injective (by rw [hj, hj, e]))
  obtain ⟨T, hT, hTgood⟩ :=
    exists_finite_forall_liesOver (K := K) (eventually_goodReduction E hEj)
  refine ⟨T, hT, fun 𝔭 h𝔭T h𝔭1 𝔓 _ ↦ ?_⟩
  have hv := absNorm_prime_of_mem_degreeOnePrimes h𝔭1
  obtain ⟨W, hWell, hWmap, hWj, hWres⟩ := hTgood 𝔭 h𝔭T 𝔓 inferInstance
  have partB : ∀ (x : ELL K)
      (φ : Isogeny (E x) (E ((ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x))),
      (homConstSet ((E x).baseChange ℂ)
          ((E ((ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x)).baseChange ℂ) : Set ℂ) =
        (algebraMap L ℂ (invConst φ) * ·) ''
          idealLattice (algebraMap K ℂ) (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹ →
      ∀ (W W' : WeierstrassCurve (localizationAt L 𝔓)) [W.IsElliptic] [W'.IsElliptic]
        (hW : W.map (algebraMap (localizationAt L 𝔓) L) = E x)
        (hW' : W'.map (algebraMap (localizationAt L 𝔓) L) =
          E ((ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x))
        (p : ℕ) [Fact p.Prime] [CharP (ResidueField (localizationAt L 𝔓)) p],
        p = Ideal.absNorm 𝔭.asIdeal ∧ φ.degree = p ∧
          (∃ ψ : Isogeny (frobeniusTwist (W.map (IsLocalRing.residue _)) p)
              (W'.map (IsLocalRing.residue _)),
            reduceIsogeny L W W' (φ.congr hW.symm hW'.symm) =
              ψ.comp (frobeniusIsogeny (W.map (IsLocalRing.residue _)) p) ∧
            ψ.degree = 1 ∧ (dualOver ψ).comp ψ = mulIsogeny _ 1 one_ne_zero ∧
            ψ.comp (dualOver ψ) = mulIsogeny _ 1 one_ne_zero) ∧
          IsLocalRing.residue _ W'.j = IsLocalRing.residue _ W.j ^ p := by
    intro x φ hφ W W' _ _ hW hW' q _ _
    obtain ⟨h₁, -⟩ := hE x
    obtain ⟨h₂, -⟩ := hE ((ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x)
    exact reduceIsogeny_congr_eq_comp_frobeniusIsogeny hK 𝔭 hv 𝔓 h₁ h₂ φ hφ hW hW' q
  refine ⟨⟨W, hWell, hWmap, hWres⟩, fun σ hσ ↦ ?_, partB⟩

  set p := Ideal.absNorm 𝔭.asIdeal with hpdef
  have : Fact p.Prime := ⟨hv⟩
  have : CharP (ResidueField (localizationAt L 𝔓)) p := by
    refine charP_residueField_localizationAt 𝔓 hv ?_
    have := algebraMap_mem_of_liesOver (𝔓 := 𝔓) (Ideal.absNorm_mem 𝔭.asIdeal)
    rwa [map_natCast] at this
  set x₀ : ELL K := classToEll (algebraMap K ℂ) hK 1
  set y := (ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x₀
  set z := (ellMulAction (algebraMap K ℂ) hK).smul (galClassOf hK L hL σ) x₀
  obtain ⟨φ, hφ, -⟩ := exists_isogeny_primeClass_smul hK E hE hiso 𝔭 x₀
  obtain ⟨-, -, -, hjy⟩ := partB x₀ φ hφ (W x₀) (W y) (hWmap x₀) (hWmap y) p
  have hjmem : (E x₀).j ∈ localizationAt L 𝔓 := by
    rw [← hWj x₀]
    exact (W x₀).j.2
  obtain ⟨hσmem, hσres⟩ := residue_apply_of_isArithFrobAt 𝔓 hσ hjmem
  have hq : Nat.card (𝓞 K ⧸ 𝔓.asIdeal.under (𝓞 K)) = p := by
    rw [← Ideal.LiesOver.over (P := 𝔓.asIdeal) (p := 𝔭.asIdeal), hpdef, Ideal.absNorm_apply,
      Submodule.cardQuot_apply]
  have hσj : σ (E x₀).j = (E z).j := by
    have h := galClassOf_apply_j hK L hL σ x₀
    have e1 : (⟨ELL.j x₀, hL x₀⟩ : L) = (E x₀).j := Subtype.ext (hj x₀)
    rw [e1] at h
    apply Subtype.ext
    rw [h, hj z]
    rfl
  have key : IsLocalRing.residue _ (W z).j = IsLocalRing.residue _ (W y).j := by
    have ez : (W z).j = ⟨σ (E x₀).j, hσmem⟩ := Subtype.ext (by
      show ((W z).j : L) = σ (E x₀).j
      rw [hσj, ← hWj z]
      rfl)
    have ex : (W x₀).j = ⟨(E x₀).j, hjmem⟩ := Subtype.ext (by
      show ((W x₀).j : L) = (E x₀).j
      rw [← hWj x₀]
      rfl)
    rw [ez, hσres, hq, hjy, ex]
  have hzy : z = y := by
    by_contra hne
    exact hWres hne key
  have hcls : galClassOf hK L hL σ = primeClass 𝔭 := by
    obtain ⟨a, -, huniq⟩ := existsUnique_smul_eq (algebraMap K ℂ) hK x₀ y
    exact (huniq _ hzy).trans (huniq _ rfl).symm
  refine ⟨hcls, fun x ↦ Subtype.ext ?_⟩
  rw [galClassOf_apply_j, hcls]

end Global

end

end Elliptic
end GroundTheory.Global
end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.GlobalFields.ComplexMultiplication.FrobeniusAtPrimes =====
