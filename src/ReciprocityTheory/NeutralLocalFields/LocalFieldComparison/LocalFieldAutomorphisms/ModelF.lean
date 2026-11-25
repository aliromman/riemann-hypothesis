module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.Algebra.Valued.ValuativeRel
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.Kloc
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Tactic.TypeStar
import Formalism.ConjugateSelfDual.Statement
import ReciprocityTheory.GaloisValuations.GlobalA

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.ModelA, ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.ModelF

-- ===== clump member: ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.ModelA =====
-- clump-header: {"m": "ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.ModelA", "h": "module\n\npublic import Mathlib.NumberTheory.NumberField.Basic\npublic import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic\npublic import Mathlib.RingTheory.Flat.TorsionFree\npublic import Mathlib.RingTheory.Henselian\npublic import Mathlib.RingTheory.RegularLocalRing.Defs\npublic import Mathlib.RingTheory.SimpleRing.Principal\npublic import Mathlib.Topology.Algebra.Valued.ValuativeRel\npublic import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.Kloc\nimport Formalism.ConjugateSelfDual.Statement\nimport ReciprocityTheory.GaloisValuations.GlobalA\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace ReciprocityTheory.Neutral.Cmp

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain ValuativeRel

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]

def locVal (ι : Ω →+* PadicAlgCl p) : Valuation (Kloc F ι) NNReal :=
  (PadicAlgCl.valued p).v.comap (algebraMap (Kloc F ι) (PadicAlgCl p))

theorem locVal_apply (ι : Ω →+* PadicAlgCl p) (x : Kloc F ι) : ((locVal ι x : NNReal) : ℝ) = ‖(x : PadicAlgCl p)‖ :=
  rfl

@[instance_reducible]
def locRel (ι : Ω →+* PadicAlgCl p) : ValuativeRel (Kloc F ι) := .ofValuation (locVal ι)

attribute [local instance] locRel

theorem locVal_compat (ι : Ω →+* PadicAlgCl p) : (locVal (F := F) ι).Compatible := Valuation.Compatible.ofValuation _

theorem valuation_lt_iff_Kloc (ι : Ω →+* PadicAlgCl p) (x y : Kloc F ι) :
    valuation (Kloc F ι) x < valuation (Kloc F ι) y ↔ ‖(x : PadicAlgCl p)‖ < ‖(y : PadicAlgCl p)‖ := by
  have := locVal_compat (F := F) ι
  rw [(ValuativeRel.isEquiv (valuation (Kloc F ι)) (locVal ι)).lt_iff_lt, ← NNReal.coe_lt_coe,
    locVal_apply, locVal_apply]

theorem valuation_le_iff_Kloc (ι : Ω →+* PadicAlgCl p) (x y : Kloc F ι) :
    valuation (Kloc F ι) x ≤ valuation (Kloc F ι) y ↔ ‖(x : PadicAlgCl p)‖ ≤ ‖(y : PadicAlgCl p)‖ := by
  rw [← not_lt, valuation_lt_iff_Kloc, not_lt]

theorem mem_integer_Kloc (ι : Ω →+* PadicAlgCl p) (x : Kloc F ι) :
    x ∈ 𝒪[Kloc F ι] ↔ ‖(x : PadicAlgCl p)‖ ≤ 1 := by
  have h := valuation_le_iff_Kloc ι x 1
  rw [map_one] at h
  rw [Valuation.mem_integer_iff, h]
  simp

end ReciprocityTheory.Neutral.Cmp
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.ModelA =====

-- ===== clump member: ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.ModelF =====
-- clump-header: {"m": "ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.ModelF", "h": "module\n\npublic import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.ModelA\npublic import Mathlib.NumberTheory.Padics.PadicIntegers\npublic import Mathlib.NumberTheory.Padics.RingHoms\nimport Mathlib.Tactic.TypeStar\nimport Formalism.ConjugateSelfDual.Statement\nimport ReciprocityTheory.GaloisValuations.GlobalA\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace ReciprocityTheory.Neutral.Cmp

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain ValuativeRel

theorem card_quot_natCast_padicInt (p : ℕ) [Fact p.Prime] {n : ℕ} (hn : n ≠ 0) :
    Nat.card (ℤ_[p] ⧸ Ideal.span {(n : ℤ_[p])}) = p ^ padicValNat p n := by
  have hp := (Fact.out : p.Prime)
  have hdec : n = p ^ padicValNat p n * (n / p ^ padicValNat p n) := by
    have h1 := Nat.ordProj_mul_ordCompl_eq_self n p
    rw [Nat.factorization_def n hp, ← Nat.padicValNat_def] at h1
    exact h1.symm
  have hnd : ¬ p ∣ n / p ^ padicValNat p n := by
    have h1 := Nat.not_dvd_ordCompl hp hn
    rwa [Nat.factorization_def n hp, ← Nat.padicValNat_def] at h1
  have hu : IsUnit (((n / p ^ padicValNat p n : ℕ) : ℤ_[p])) :=
    PadicInt.isUnit_iff.mpr
      (PadicInt.norm_natCast_eq_one_iff.mpr (hp.coprime_iff_not_dvd.mpr hnd))
  have hspan : Ideal.span {(n : ℤ_[p])} = Ideal.span {(p : ℤ_[p]) ^ padicValNat p n} := by
    conv_lhs => rw [hdec]
    push_cast
    exact Ideal.span_singleton_mul_right_unit hu _
  rw [hspan, ← PadicInt.ker_toZModPow]
  rw [Nat.card_congr (RingHom.quotientKerEquivOfSurjective
    (ZMod.ringHom_surjective (PadicInt.toZModPow (p := p) (padicValNat p n)))).toEquiv, Nat.card_zmod]

theorem card_quot_span_algebraMap {R C ι : Type*} [CommRing R] [CommRing C] [Algebra R C] [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι R C) (r : R) :
    Nat.card (C ⧸ Ideal.span {algebraMap R C r}) = Nat.card (R ⧸ Ideal.span {r}) ^ Fintype.card ι := by
  let φ : C →ₗ[R] (ι → R ⧸ Ideal.span {r}) :=
    LinearMap.pi fun i => (Ideal.span {r}).mkQ ∘ₗ b.coord i
  have hφ : Function.Surjective φ := by
    intro y
    choose c hc using fun i => Ideal.Quotient.mk_surjective (y i)
    refine ⟨b.equivFun.symm c, ?_⟩
    funext i
    have h1 : b.repr (b.equivFun.symm c) i = c i := by
      rw [← b.equivFun_apply, LinearEquiv.apply_symm_apply]
    simp only [φ, LinearMap.pi_apply, LinearMap.comp_apply, Module.Basis.coord_apply, Submodule.mkQ_apply, h1]
    exact hc i
  have hker : LinearMap.ker φ = (Ideal.span {algebraMap R C r}).restrictScalars R := by
    ext x
    simp only [LinearMap.mem_ker, Submodule.restrictScalars_mem, Ideal.mem_span_singleton']
    constructor
    · intro hx
      have : ∀ i, ∃ a, a * r = b.repr x i := fun i => by
        rw [← Ideal.mem_span_singleton', ← Ideal.Quotient.eq_zero_iff_mem]
        simpa [φ] using congrFun hx i
      choose a ha using this
      refine ⟨b.equivFun.symm a, ?_⟩
      apply b.repr.injective
      ext i
      rw [mul_comm, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, ← b.equivFun_apply,
        LinearEquiv.apply_symm_apply, ← ha, smul_eq_mul, mul_comm]
    · rintro ⟨a, rfl⟩
      funext i
      rw [mul_comm, ← Algebra.smul_def]
      simp only [φ, LinearMap.pi_apply, LinearMap.comp_apply, Module.Basis.coord_apply, map_smul,
        Submodule.mkQ_apply, Pi.zero_apply]
      exact (Submodule.Quotient.mk_eq_zero _).2 (Ideal.mem_span_singleton.2 (dvd_mul_right _ _))
  have e := ((Submodule.Quotient.restrictScalarsEquiv R (Ideal.span {algebraMap R C r})).symm.trans
    (Submodule.quotEquivOfEq _ _ hker.symm)).trans (φ.quotKerEquivOfSurjective hφ)
  rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := ι)]

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]

attribute [local instance] locRel

theorem norm_algebraMap_padicInt_Kloc (ι : Ω →+* PadicAlgCl p) (x : ℤ_[p]) :
    ‖((algebraMap ℤ_[p] (Kloc F ι) x : Kloc F ι) : PadicAlgCl p)‖ ≤ 1 := by
  show ‖algebraMap ℚ_[p] (PadicAlgCl p) (x : ℚ_[p])‖ ≤ 1
  exact (PadicAlgCl.norm_extends p (x : ℚ_[p])).le.trans x.2

def zpToInteger (ι : Ω →+* PadicAlgCl p) : ℤ_[p] →+* 𝒪[Kloc F ι] :=
  (algebraMap ℤ_[p] (Kloc F ι)).codRestrict _
    fun x => (mem_integer_Kloc ι _).2 (norm_algebraMap_padicInt_Kloc ι x)

@[instance_reducible]
def zpAlgInteger (ι : Ω →+* PadicAlgCl p) : Algebra ℤ_[p] 𝒪[Kloc F ι] := (zpToInteger (F := F) ι).toAlgebra

attribute [local instance] zpAlgInteger

end ReciprocityTheory.Neutral.Cmp
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.ModelF =====
