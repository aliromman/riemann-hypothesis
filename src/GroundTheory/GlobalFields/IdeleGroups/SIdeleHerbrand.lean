module

public import GroundTheory.GlobalFields.IdeleGroups.LocalHerbrandInfinite
public import GroundTheory.GlobalFields.IdeleGroups.LocalHerbrand
public import GroundTheory.GlobalFields.IdeleGroups.SIdeleGroups.InfinitePlaces
public import GroundTheory.GlobalFields.IdeleGroups.SIdeleGroups.IntegerUnits
public import GroundTheory.GlobalFields.HerbrandQuotients.CycTateNegOneOrbitEquivSymmMk
public import GroundTheory.GlobalFields.IdeleGroups.SIdeleGroups.Galois
public import GroundTheory.GlobalFields.IdeleGroups.SIdeleGroups.Decomposition
import Mathlib.Tactic.TypeStar

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: GroundTheory.GlobalFields.IdeleGroups.SIdeleHerbrand.Product, GroundTheory.GlobalFields.IdeleGroups.SIdeleHerbrand.Places, GroundTheory.GlobalFields.IdeleGroups.SIdeleHerbrand

-- ===== clump member: GroundTheory.GlobalFields.IdeleGroups.SIdeleHerbrand.Product =====
-- clump-header: {"m": "GroundTheory.GlobalFields.IdeleGroups.SIdeleHerbrand.Product", "h": "module\n\npublic import GroundTheory.GlobalFields.HerbrandQuotients.CycTateNegOneOrbitEquivSymmMk\nimport Mathlib.Tactic.TypeStar\n\n"}
section -- clump:auto
@[expose] public section

namespace GroundTheory.Global

open GroundTheory.GroupCoh

noncomputable section

section KerModRangeProd

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

def kerModRangeProdEquiv (F G : A × B →+ A × B) (fA gA : A →+ A) (fB gB : B →+ B)
    (hF : ∀ x, F x = (fA x.1, fB x.2)) (hG : ∀ x, G x = (gA x.1, gB x.2)) :
    KerModRange F G ≃+ KerModRange fA gA × KerModRange fB gB :=
  kerModRangeEquivOfSurjective
    (AddMonoidHom.prod
      ((QuotientAddGroup.mk' _).comp
        (((AddMonoidHom.fst A B).comp F.ker.subtype).codRestrict fA.ker fun x ↦
          AddMonoidHom.mem_ker.2 (congrArg Prod.fst ((hF x).symm.trans (AddMonoidHom.mem_ker.1 x.2)))))
      ((QuotientAddGroup.mk' _).comp
        (((AddMonoidHom.snd A B).comp F.ker.subtype).codRestrict fB.ker fun x ↦
          AddMonoidHom.mem_ker.2 (congrArg Prod.snd ((hF x).symm.trans (AddMonoidHom.mem_ker.1 x.2))))))
    (by
      rintro ⟨y₁, y₂⟩
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective y₁
      obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective y₂
      refine ⟨⟨((a : A), (b : B)), AddMonoidHom.mem_ker.2 ?_⟩, rfl⟩
      rw [hF, AddMonoidHom.mem_ker.1 a.2, AddMonoidHom.mem_ker.1 b.2, Prod.mk_zero_zero])
    (by
      intro x
      constructor
      · intro h
        have h1 : (x : A × B).1 ∈ gA.range :=
          (KerModRange.mk_eq_zero_iff (g := gA) _).1 (congrArg Prod.fst h)
        have h2 : (x : A × B).2 ∈ gB.range :=
          (KerModRange.mk_eq_zero_iff (g := gB) _).1 (congrArg Prod.snd h)
        obtain ⟨a, ha⟩ := AddMonoidHom.mem_range.1 h1
        obtain ⟨b, hb⟩ := AddMonoidHom.mem_range.1 h2
        exact AddMonoidHom.mem_range.2 ⟨(a, b), by rw [hG, ha, hb]⟩
      · intro h
        obtain ⟨y, hy⟩ := AddMonoidHom.mem_range.1 h
        rw [hG] at hy
        exact Prod.ext
          ((KerModRange.mk_eq_zero_iff (g := gA) _).2
            (AddMonoidHom.mem_range.2 ⟨y.1, congrArg Prod.fst hy⟩))
          ((KerModRange.mk_eq_zero_iff (g := gB) _).2
            (AddMonoidHom.mem_range.2 ⟨y.2, congrArg Prod.snd hy⟩)))

end KerModRangeProd

section Prod

variable {k G V W : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V] [AddCommGroup W]
  [Module k W]

theorem cycSubOne_prod_apply (ρ : Representation k G V) (ρ' : Representation k G W) (σ : G)
    (x : V × W) : cycSubOne (ρ.prod ρ') σ x = (cycSubOne ρ σ x.1, cycSubOne ρ' σ x.2) := by
  rw [cycSubOne_apply, cycSubOne_apply, cycSubOne_apply]
  rfl

variable [Fintype G]

theorem cycNorm_prod_apply (ρ : Representation k G V) (ρ' : Representation k G W)
    (x : V × W) : cycNorm (ρ.prod ρ') x = (cycNorm ρ x.1, cycNorm ρ' x.2) := by
  rw [cycNorm_apply, cycNorm_apply, cycNorm_apply]
  exact Prod.ext (by rw [Prod.fst_sum]; rfl) (by rw [Prod.snd_sum]; rfl)

def cycTateZeroProdEquiv (ρ : Representation k G V) (ρ' : Representation k G W) (σ : G) :
    CycTateZero (ρ.prod ρ') σ ≃+ CycTateZero ρ σ × CycTateZero ρ' σ :=
  kerModRangeProdEquiv _ _ _ _ _ _ (cycSubOne_prod_apply ρ ρ' σ) (cycNorm_prod_apply ρ ρ')

def cycTateNegOneProdEquiv (ρ : Representation k G V) (ρ' : Representation k G W) (σ : G) :
    CycTateNegOne (ρ.prod ρ') σ ≃+ CycTateNegOne ρ σ × CycTateNegOne ρ' σ :=
  kerModRangeProdEquiv _ _ _ _ _ _ (cycNorm_prod_apply ρ ρ') (cycSubOne_prod_apply ρ ρ' σ)

theorem cycHerbrand_prod_eq_mul (ρ : Representation k G V) (ρ' : Representation k G W) (σ : G) :
    cycHerbrand (ρ.prod ρ') σ = cycHerbrand ρ σ * cycHerbrand ρ' σ := by
  simp only [cycHerbrand_eq]
  rw [Nat.card_congr (cycTateZeroProdEquiv ρ ρ' σ).toEquiv,
    Nat.card_congr (cycTateNegOneProdEquiv ρ ρ' σ).toEquiv, Nat.card_prod, Nat.card_prod,
    Nat.cast_mul, Nat.cast_mul, mul_div_mul_comm]

end Prod

section Mul

variable {G : Type*} [Group G]

def additiveProdEquiv (M N : Type*) [CommGroup M] [CommGroup N] :
    Additive (M × N) ≃+ Additive M × Additive N where
  toFun x := (Additive.ofMul x.toMul.1, Additive.ofMul x.toMul.2)
  invFun y := Additive.ofMul (y.1.toMul, y.2.toMul)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

def additivePiEquiv {ι : Type*} (M : ι → Type*) [∀ i, CommGroup (M i)] :
    Additive (∀ i, M i) ≃+ ∀ i, Additive (M i) where
  toFun x i := Additive.ofMul (x.toMul i)
  invFun y := Additive.ofMul fun i ↦ (y i).toMul
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

section Prod

variable (M N : Type*) [CommGroup M] [CommGroup N] [MulDistribMulAction G M]
  [MulDistribMulAction G N] [Fintype G]

theorem cycHerbrand_mulProd (σ : G) :
    cycHerbrand (Representation.ofMulDistribMulAction G (M × N)) σ =
      cycHerbrand (Representation.ofMulDistribMulAction G M) σ *
        cycHerbrand (Representation.ofMulDistribMulAction G N) σ := by
  rw [cycHerbrand_congr (ρ' := (Representation.ofMulDistribMulAction G M).prod
      (Representation.ofMulDistribMulAction G N)) (additiveProdEquiv M N) (fun _ _ ↦ rfl) σ,
    cycHerbrand_prod_eq_mul]

end Prod

section Pi

variable {ι : Type*} (M : ι → Type*) [∀ i, CommGroup (M i)] [∀ i, MulDistribMulAction G (M i)]
  [Fintype G]

def cycTateZeroMulPiEquiv (σ : G) :
    CycTateZero (Representation.ofMulDistribMulAction G (∀ i, M i)) σ ≃+
      ∀ i, CycTateZero (Representation.ofMulDistribMulAction G (M i)) σ :=
  (cycTateZeroCongr (ρ' := piRep fun i ↦ Representation.ofMulDistribMulAction G (M i))
      (additivePiEquiv M) (fun _ _ ↦ rfl) σ).trans (cycTateZeroPiEquiv _ σ)

def cycTateNegOneMulPiEquiv (σ : G) :
    CycTateNegOne (Representation.ofMulDistribMulAction G (∀ i, M i)) σ ≃+
      ∀ i, CycTateNegOne (Representation.ofMulDistribMulAction G (M i)) σ :=
  (cycTateNegOneCongr (ρ' := piRep fun i ↦ Representation.ofMulDistribMulAction G (M i))
      (additivePiEquiv M) (fun _ _ ↦ rfl) σ).trans (cycTateNegOnePiEquiv _ σ)

theorem cycHerbrand_mulPi [Fintype ι] (σ : G) :
    cycHerbrand (Representation.ofMulDistribMulAction G (∀ i, M i)) σ =
      ∏ i, cycHerbrand (Representation.ofMulDistribMulAction G (M i)) σ := by
  rw [cycHerbrand_congr (ρ' := piRep fun i ↦ Representation.ofMulDistribMulAction G (M i))
      (additivePiEquiv M) (fun _ _ ↦ rfl) σ, cycHerbrand_pi]

end Pi

section Orbit

variable {X : Type*} {U : X → Type*} [∀ x, CommGroup (U x)] [MulDistribMulAction G (∀ x, U x)]


variable (G U) in
def mulPiRep : Representation ℤ G (∀ x, Additive (U x)) where
  toFun g := AddMonoidHom.toIntLinearMap ((additivePiEquiv U).toAddMonoidHom.comp
    ((Representation.ofMulDistribMulAction G (∀ x, U x) g).toAddMonoidHom.comp
      (additivePiEquiv U).symm.toAddMonoidHom))
  map_one' := LinearMap.ext fun y ↦ funext fun x ↦
    congrArg (fun f : ∀ x, U x ↦ Additive.ofMul (f x)) (one_smul G fun x ↦ (y x).toMul)
  map_mul' g h := LinearMap.ext fun y ↦ funext fun x ↦
    congrArg (fun f : ∀ x, U x ↦ Additive.ofMul (f x)) (mul_smul g h fun x ↦ (y x).toMul)

variable [MulAction G X]

theorem permutesFactors_mulPiRep
    (h : ∀ (g : G) (f : ∀ x, U x) (x : X), f x = 1 → (g • f) (g • x) = 1) :
    PermutesFactors (mulPiRep (G := G) (U := U)) := fun g f x hf ↦
  congrArg Additive.ofMul (h g (fun x ↦ (f x).toMul) x hf)

variable [Fintype G] [MulAction.IsPretransitive G X]

def cycTateZeroMulOrbitEquiv
    (hU : ∀ (g : G) (f : ∀ x, U x) (x : X), f x = 1 → (g • f) (g • x) = 1) (x₀ : X)
    (D : Subgroup G) [Fintype D] (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀) [MulDistribMulAction D (U x₀)]
    (hU₀ : ∀ (d : D) (f : ∀ x, U x), ((d : G) • f) x₀ = d • f x₀) (σ : G)
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (τ : D) (hτ : ∀ d, d ∈ Subgroup.zpowers τ) :
    CycTateZero (Representation.ofMulDistribMulAction G (∀ x, U x)) σ ≃+
      CycTateZero (Representation.ofMulDistribMulAction D (U x₀)) τ :=
  (cycTateZeroCongr (ρ' := mulPiRep (G := G) (U := U)) (additivePiEquiv U)
    (fun _ _ ↦ rfl) σ).trans
    (cycTateZeroOrbitEquiv (mulPiRep (G := G) (U := U)) (permutesFactors_mulPiRep hU) x₀ D hD
      (Representation.ofMulDistribMulAction D (U x₀))
      (fun d f ↦ congrArg Additive.ofMul (hU₀ d fun x ↦ (f x).toMul)) σ hσ τ hτ)

def cycTateNegOneMulOrbitEquiv
    (hU : ∀ (g : G) (f : ∀ x, U x) (x : X), f x = 1 → (g • f) (g • x) = 1) (x₀ : X)
    (D : Subgroup G) [Fintype D] (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀) [MulDistribMulAction D (U x₀)]
    (hU₀ : ∀ (d : D) (f : ∀ x, U x), ((d : G) • f) x₀ = d • f x₀) (σ : G)
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (τ : D) (hτ : ∀ d, d ∈ Subgroup.zpowers τ) :
    CycTateNegOne (Representation.ofMulDistribMulAction G (∀ x, U x)) σ ≃+
      CycTateNegOne (Representation.ofMulDistribMulAction D (U x₀)) τ :=
  (cycTateNegOneCongr (ρ' := mulPiRep (G := G) (U := U)) (additivePiEquiv U)
    (fun _ _ ↦ rfl) σ).trans
    (cycTateNegOneOrbitEquiv (mulPiRep (G := G) (U := U)) (permutesFactors_mulPiRep hU) x₀ D hD
      (Representation.ofMulDistribMulAction D (U x₀))
      (fun d f ↦ congrArg Additive.ofMul (hU₀ d fun x ↦ (f x).toMul)) σ hσ τ hτ)

theorem cycHerbrand_mulOrbit
    (hU : ∀ (g : G) (f : ∀ x, U x) (x : X), f x = 1 → (g • f) (g • x) = 1) (x₀ : X)
    (D : Subgroup G) [Fintype D] (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀) [MulDistribMulAction D (U x₀)]
    (hU₀ : ∀ (d : D) (f : ∀ x, U x), ((d : G) • f) x₀ = d • f x₀) (σ : G)
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (τ : D) (hτ : ∀ d, d ∈ Subgroup.zpowers τ) :
    cycHerbrand (Representation.ofMulDistribMulAction G (∀ x, U x)) σ =
      cycHerbrand (Representation.ofMulDistribMulAction D (U x₀)) τ := by
  rw [cycHerbrand_eq, cycHerbrand_eq,
    Nat.card_congr (cycTateZeroMulOrbitEquiv hU x₀ D hD hU₀ σ hσ τ hτ).toEquiv,
    Nat.card_congr (cycTateNegOneMulOrbitEquiv hU x₀ D hD hU₀ σ hσ τ hτ).toEquiv]

end Orbit

end Mul

end

end GroundTheory.Global
end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.GlobalFields.IdeleGroups.SIdeleHerbrand.Product =====

-- ===== clump member: GroundTheory.GlobalFields.IdeleGroups.SIdeleHerbrand.Places =====
-- clump-header: {"m": "GroundTheory.GlobalFields.IdeleGroups.SIdeleHerbrand.Places", "h": "module\n\npublic import GroundTheory.GlobalFields.IdeleGroups.LocalHerbrandInfinite\npublic import GroundTheory.GlobalFields.IdeleGroups.LocalHerbrand\npublic import GroundTheory.GlobalFields.IdeleGroups.SIdeleGroups.InfinitePlaces\npublic import GroundTheory.GlobalFields.IdeleGroups.SIdeleGroups.IntegerUnits\npublic import GroundTheory.GlobalFields.IdeleGroups.SIdeleHerbrand.Product\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace GroundTheory.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum GroundTheory.GroupCoh
  AdeleBaseChange SemiLocal

open scoped Pointwise NumberField.LiesOver

noncomputable section

namespace IdeleGroup

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

section Finite

variable (v : HeightOneSpectrum (𝓞 K))


omit [NumberField K] [NumberField L] in
theorem mem_stabilizer_iff_smul_placesOver (w : PlacesOver L v) (σ : Gal(L/K)) :
    σ ∈ MulAction.stabilizer Gal(L/K) w.1.asIdeal ↔ σ • w = w := by
  rw [MulAction.mem_stabilizer_iff, Subtype.ext_iff, coe_smul_placesOver,
    HeightOneSpectrum.ext_iff, smul_asIdeal]

theorem finiteUnitsAbove_smul_apply_of_eq (σ : Gal(L/K))
    (y : (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ) (w w' : PlacesOver L v)
    (h : w' = σ • w) :
    (((σ • y) w' : (w'.1.adicCompletion L)ˣ) : w'.1.adicCompletion L) =
      galEquiv v σ w.1 w'.1 (by rw [h]; rfl) (y w) := by
  subst h
  exact finiteUnitsAbove_smul_apply v σ y w


omit [NumberField K] in
theorem galHom_eq_decomposition_smul (w : PlacesOver L v)
    (σ : MulAction.stabilizer Gal(L/K) w.1.asIdeal) (h : w.1 = (σ : Gal(L/K)) • w.1)
    (x : w.1.adicCompletion L) : galHom (σ : Gal(L/K)) w.1 w.1 h x = σ • x := by
  rw [decomposition_smul_def]
  exact congrFun (congrArg DFunLike.coe (ringHom_ext_adicCompletion w.1
    (continuous_galHom _ _ _ h) (continuous_adicCompletionRingHomOf _ _) fun y ↦ by
      rw [galHom_algebraMap, adicCompletionRingHomOf_algebraMap])) x

theorem finiteUnitsAbove_smul_apply_self (w : PlacesOver L v)
    (σ : MulAction.stabilizer Gal(L/K) w.1.asIdeal)
    (y : (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ) : ((σ : Gal(L/K)) • y) w = σ • y w := by
  have hw : w = (σ : Gal(L/K)) • w :=
    ((mem_stabilizer_iff_smul_placesOver v w σ).1 σ.2).symm
  apply Units.ext
  rw [finiteUnitsAbove_smul_apply_of_eq v _ y w w hw, galEquiv_apply,
    galHom_eq_decomposition_smul]
  rfl

theorem finiteUnitsAbove_smul_apply_eq_one (σ : Gal(L/K))
    (y : (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ) (w : PlacesOver L v) (hy : y w = 1) :
    (σ • y) (σ • w) = 1 :=
  Units.ext (by rw [finiteUnitsAbove_smul_apply, hy, Units.val_one, map_one, Units.val_one])

theorem integerUnitsAbove_smul_apply_self (w : PlacesOver L v)
    (σ : MulAction.stabilizer Gal(L/K) w.1.asIdeal)
    (z : (w : PlacesOver L v) → (w.1.adicCompletionIntegers L)ˣ) :
    ((σ : Gal(L/K)) • z) w = σ • z w := by
  apply Units.ext
  apply Subtype.ext
  rw [coe_decomposition_smul_integerUnits, ← coe_integerUnitsAboveIncl_apply,
    integerUnitsAboveIncl_smul, finiteUnitsAbove_smul_apply_self, coe_decomposition_smul_units,
    coe_integerUnitsAboveIncl_apply]

theorem integerUnitsAbove_smul_apply_eq_one (σ : Gal(L/K))
    (z : (w : PlacesOver L v) → (w.1.adicCompletionIntegers L)ˣ) (w : PlacesOver L v)
    (hz : z w = 1) : (σ • z) (σ • w) = 1 := by
  apply Units.ext
  apply Subtype.ext
  rw [integerUnitsAbove_smul_apply, hz, Units.val_one, OneMemClass.coe_one, map_one,
    Units.val_one, OneMemClass.coe_one]

variable [IsGalois K L] [Fintype Gal(L/K)]


open AdicLiesOver in
theorem cycHerbrand_finiteUnitsAbove (σ : Gal(L/K)) (hσ : ∀ g, g ∈ Subgroup.zpowers σ)
    (w : PlacesOver L v) :
    cycHerbrand (Representation.ofMulDistribMulAction Gal(L/K)
        ((u : PlacesOver L v) → (u.1.adicCompletion L)ˣ)) σ =
      Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) := by
  have : IsCyclic Gal(L/K) := ⟨⟨σ, fun g ↦ Subgroup.mem_zpowers_iff.1 (hσ g)⟩⟩
  obtain ⟨τ, hτ⟩ := IsCyclic.exists_generator (α := MulAction.stabilizer Gal(L/K) w.1.asIdeal)
  let _ : Fintype (MulAction.stabilizer Gal(L/K) w.1.asIdeal) := Fintype.ofFinite _
  rw [cycHerbrand_mulOrbit (U := fun u : PlacesOver L v ↦ (u.1.adicCompletion L)ˣ)
    (finiteUnitsAbove_smul_apply_eq_one v) w _ (mem_stabilizer_iff_smul_placesOver v w)
    (finiteUnitsAbove_smul_apply_self v w) σ hσ τ hτ]
  exact (cycHerbrand_adicCompletion_units v w.1 τ hτ).2

theorem subsingleton_cycTateZero_integerUnitsAbove (σ : Gal(L/K))
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (w : PlacesOver L v)
    (he : w.1.asIdeal.ramificationIdx (𝓞 K) = 1) :
    Subsingleton (CycTateZero (Representation.ofMulDistribMulAction Gal(L/K)
      ((u : PlacesOver L v) → (u.1.adicCompletionIntegers L)ˣ)) σ) := by
  have : IsCyclic Gal(L/K) := ⟨⟨σ, fun g ↦ Subgroup.mem_zpowers_iff.1 (hσ g)⟩⟩
  obtain ⟨τ, hτ⟩ := IsCyclic.exists_generator (α := MulAction.stabilizer Gal(L/K) w.1.asIdeal)
  let _ : Fintype (MulAction.stabilizer Gal(L/K) w.1.asIdeal) := Fintype.ofFinite _
  have := subsingleton_cycTateZero_adicCompletionIntegers_units v w.1 he τ hτ
  exact (cycTateZeroMulOrbitEquiv (U := fun u : PlacesOver L v ↦ (u.1.adicCompletionIntegers L)ˣ)
    (integerUnitsAbove_smul_apply_eq_one v) w _ (mem_stabilizer_iff_smul_placesOver v w)
    (integerUnitsAbove_smul_apply_self v w) σ hσ τ hτ).toEquiv.subsingleton

theorem subsingleton_cycTateNegOne_integerUnitsAbove (σ : Gal(L/K))
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (w : PlacesOver L v)
    (he : w.1.asIdeal.ramificationIdx (𝓞 K) = 1) :
    Subsingleton (CycTateNegOne (Representation.ofMulDistribMulAction Gal(L/K)
      ((u : PlacesOver L v) → (u.1.adicCompletionIntegers L)ˣ)) σ) := by
  have : IsCyclic Gal(L/K) := ⟨⟨σ, fun g ↦ Subgroup.mem_zpowers_iff.1 (hσ g)⟩⟩
  obtain ⟨τ, hτ⟩ := IsCyclic.exists_generator (α := MulAction.stabilizer Gal(L/K) w.1.asIdeal)
  let _ : Fintype (MulAction.stabilizer Gal(L/K) w.1.asIdeal) := Fintype.ofFinite _
  have := subsingleton_cycTateNegOne_adicCompletionIntegers_units v w.1 he τ hτ
  exact (cycTateNegOneMulOrbitEquiv
    (U := fun u : PlacesOver L v ↦ (u.1.adicCompletionIntegers L)ˣ)
    (integerUnitsAbove_smul_apply_eq_one v) w _ (mem_stabilizer_iff_smul_placesOver v w)
    (integerUnitsAbove_smul_apply_self v w) σ hσ τ hτ).toEquiv.subsingleton

end Finite

section Infinite

def infiniteCompletionCongr {u u' : InfinitePlace L} (h : u = u') :
    u.Completion ≃+* u'.Completion :=
  h ▸ RingEquiv.refl _

omit [NumberField L] in
theorem continuous_infiniteCompletionCongr {u u' : InfinitePlace L} (h : u = u') :
    Continuous (infiniteCompletionCongr h) := by
  subst h
  exact continuous_id

omit [NumberField L] in
theorem infiniteCompletionCongr_algebraMap {u u' : InfinitePlace L} (h : u = u') (x : L) :
    infiniteCompletionCongr h (algebraMap L u.Completion x) = algebraMap L u'.Completion x := by
  subst h
  rfl

theorem continuous_infiniteCompletionMap {M M' : Type*} [Field M] [NumberField M] [Field M']
    [NumberField M'] (τ : M ≃+* M') (w' : InfinitePlace M') :
    Continuous (infiniteCompletionMap τ w') := by
  let _ : Algebra M M' := (τ : M →+* M').toAlgebra
  change Continuous (algebraMap (w'.comap (algebraMap M M')).Completion w'.Completion)
  exact continuous_algebraMap _ _

variable (v : InfinitePlace K)

theorem infiniteUnitsAbove_smul_apply_of_eq (σ : Gal(L/K))
    (y : (w : v.placesOver L) → (w.1.Completion)ˣ) (u w : v.placesOver L)
    (h : u.1 = w.1.comap ((σ : L ≃+* L) : L →+* L)) :
    (((σ • y) w : (w.1.Completion)ˣ) : w.1.Completion) =
      infiniteCompletionMap (σ : L ≃+* L) w.1 (infiniteCompletionCongr h (y u)) := by
  obtain rfl : u = ⟨w.1.comap ((σ : L ≃+* L) : L →+* L), comap_mem_placesOver v σ w⟩ :=
    Subtype.ext h
  exact infiniteUnitsAbove_smul_apply v σ y w

omit [NumberField K] [NumberField L] in
theorem eq_comap_smul_placesOver (σ : Gal(L/K)) (w : v.placesOver L) :
    w.1 = (σ • w).1.comap ((σ : L ≃+* L) : L →+* L) := by
  rw [comap_eq_inv_smul, InfinitePlace.coe_smul_placesOver, inv_smul_smul]

theorem infiniteUnitsAbove_smul_apply_eq_one (σ : Gal(L/K))
    (y : (w : v.placesOver L) → (w.1.Completion)ˣ) (w : v.placesOver L) (hy : y w = 1) :
    (σ • y) (σ • w) = 1 := by
  apply Units.ext
  rw [infiniteUnitsAbove_smul_apply_of_eq v σ y w (σ • w) (eq_comap_smul_placesOver v σ w), hy,
    Units.val_one, map_one, map_one, Units.val_one]


omit [NumberField K] [NumberField L] in
theorem mem_stabilizer_iff_smul_placesOver_infinite (w : v.placesOver L) (σ : Gal(L/K)) :
    σ ∈ MulAction.stabilizer Gal(L/K) w.1 ↔ σ • w = w := by
  rw [MulAction.mem_stabilizer_iff, Subtype.ext_iff, InfinitePlace.coe_smul_placesOver]


omit [NumberField K] in
theorem infiniteCompletionMap_eq_decomposition_smul (w : v.placesOver L)
    (σ : MulAction.stabilizer Gal(L/K) w.1)
    (h : w.1 = w.1.comap (((σ : Gal(L/K)) : L ≃+* L) : L →+* L)) (x : w.1.Completion) :
    infiniteCompletionMap ((σ : Gal(L/K)) : L ≃+* L) w.1 (infiniteCompletionCongr h x) =
      σ • x := by
  rw [infiniteDecomposition_smul_def]
  have := ringHom_ext_completion w.1
    (f := (infiniteCompletionMap ((σ : Gal(L/K)) : L ≃+* L) w.1).comp
      (infiniteCompletionCongr h).toRingHom)
    ((continuous_infiniteCompletionMap _ _).comp (continuous_infiniteCompletionCongr h))
    (continuous_completionRingHomOf σ.2) fun y ↦ by
      rw [completionRingHomOf_coe]
      have hy : (y : w.1.Completion) = algebraMap L w.1.Completion y.ofAbs := by
        rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply]
        rfl
      have hy' : ((withAbsMapOf w.1 (σ : Gal(L/K)) y : WithAbs w.1.1) : w.1.Completion) =
          algebraMap L w.1.Completion (withAbsMapOf w.1 (σ : Gal(L/K)) y).ofAbs := by
        rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply]
        rfl
      rw [hy, hy']
      change infiniteCompletionMap _ w.1
          (infiniteCompletionCongr h (algebraMap L w.1.Completion y.ofAbs)) =
        algebraMap L w.1.Completion (withAbsMapOf w.1 (σ : Gal(L/K)) y).ofAbs
      rw [infiniteCompletionCongr_algebraMap, infiniteCompletionMap_algebraMap,
        ofAbs_withAbsMapOf]
      rfl
  exact congrFun (congrArg DFunLike.coe this) x

theorem infiniteUnitsAbove_smul_apply_self (w : v.placesOver L)
    (σ : MulAction.stabilizer Gal(L/K) w.1) (y : (w : v.placesOver L) → (w.1.Completion)ˣ) :
    ((σ : Gal(L/K)) • y) w = σ • y w := by
  have hw : w = (σ : Gal(L/K)) • w :=
    ((mem_stabilizer_iff_smul_placesOver_infinite v w σ).1 σ.2).symm
  have h : w.1 = w.1.comap (((σ : Gal(L/K)) : L ≃+* L) : L →+* L) := by
    have h' := eq_comap_smul_placesOver v (σ : Gal(L/K)) w
    rwa [← hw] at h'
  apply Units.ext
  rw [infiniteUnitsAbove_smul_apply_of_eq v (σ : Gal(L/K)) y w w h,
    infiniteCompletionMap_eq_decomposition_smul]
  rfl

variable [IsGalois K L] [Fintype Gal(L/K)]

theorem cycHerbrand_infiniteUnitsAbove (σ : Gal(L/K)) (hσ : ∀ g, g ∈ Subgroup.zpowers σ)
    (w : v.placesOver L) :
    cycHerbrand (Representation.ofMulDistribMulAction Gal(L/K)
        ((u : v.placesOver L) → (u.1.Completion)ˣ)) σ =
      Module.finrank v.Completion w.1.Completion := by
  have : IsCyclic Gal(L/K) := ⟨⟨σ, fun g ↦ Subgroup.mem_zpowers_iff.1 (hσ g)⟩⟩
  obtain ⟨τ, hτ⟩ := IsCyclic.exists_generator (α := MulAction.stabilizer Gal(L/K) w.1)
  let _ : Fintype (MulAction.stabilizer Gal(L/K) w.1) := Fintype.ofFinite _
  rw [cycHerbrand_mulOrbit (U := fun u : v.placesOver L ↦ (u.1.Completion)ˣ)
    (infiniteUnitsAbove_smul_apply_eq_one v) w _ (mem_stabilizer_iff_smul_placesOver_infinite v w)
    (infiniteUnitsAbove_smul_apply_self v w) σ hσ τ hτ]
  exact (cycHerbrand_infiniteCompletion_units v w.1 τ hτ).2

end Infinite

end IdeleGroup

end

end GroundTheory.Global
end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.GlobalFields.IdeleGroups.SIdeleHerbrand.Places =====

-- ===== clump member: GroundTheory.GlobalFields.IdeleGroups.SIdeleHerbrand =====
-- clump-header: {"m": "GroundTheory.GlobalFields.IdeleGroups.SIdeleHerbrand", "h": "module\n\npublic import GroundTheory.GlobalFields.IdeleGroups.SIdeleHerbrand.Places\npublic import GroundTheory.GlobalFields.IdeleGroups.SIdeleGroups.Galois\npublic import GroundTheory.GlobalFields.IdeleGroups.SIdeleGroups.Decomposition\nimport GroundTheory.GlobalFields.IdeleGroups.SIdeleHerbrand.Product\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace GroundTheory.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum GroundTheory.GroupCoh

open scoped NumberField.LiesOver

open SemiLocal (PlacesOver)

noncomputable section

namespace IdeleGroup

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]


open SemiLocal in
theorem nonempty_placesOver_of_finite (v : HeightOneSpectrum (𝓞 K)) :
    Nonempty (PlacesOver L v) := by
  by_contra h
  rw [not_nonempty_iff] at h
  have := sum_finrank_eq L v
  rw [Finset.univ_eq_empty, Finset.sum_empty] at this
  exact (Module.finrank_pos (R := K) (M := L)).ne this

variable [IsGalois K L] [Fintype Gal(L/K)]

theorem subsingleton_cycTateZero_integerUnitsOutside (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v ∉ S, ∀ w : PlacesOver L v, w.1.asIdeal.ramificationIdx (𝓞 K) = 1)
    (σ : Gal(L/K)) (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    Subsingleton (CycTateZero (Representation.ofMulDistribMulAction Gal(L/K)
      ((v : ↥Sᶜ) → (w : PlacesOver L v.1) → (w.1.adicCompletionIntegers L)ˣ)) σ) := by
  have h : ∀ v : ↥Sᶜ, Subsingleton (CycTateZero (Representation.ofMulDistribMulAction Gal(L/K)
      ((w : PlacesOver L v.1) → (w.1.adicCompletionIntegers L)ˣ)) σ) := fun v ↦ by
    obtain ⟨w⟩ := nonempty_placesOver_of_finite (L := L) v.1
    exact subsingleton_cycTateZero_integerUnitsAbove v.1 σ hσ w (hS v.1 v.2 w)
  exact (cycTateZeroMulPiEquiv
    (fun v : ↥Sᶜ ↦ (w : PlacesOver L v.1) → (w.1.adicCompletionIntegers L)ˣ) σ).toEquiv.subsingleton

theorem subsingleton_cycTateNegOne_integerUnitsOutside (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v ∉ S, ∀ w : PlacesOver L v, w.1.asIdeal.ramificationIdx (𝓞 K) = 1)
    (σ : Gal(L/K)) (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    Subsingleton (CycTateNegOne (Representation.ofMulDistribMulAction Gal(L/K)
      ((v : ↥Sᶜ) → (w : PlacesOver L v.1) → (w.1.adicCompletionIntegers L)ˣ)) σ) := by
  have h : ∀ v : ↥Sᶜ, Subsingleton (CycTateNegOne (Representation.ofMulDistribMulAction Gal(L/K)
      ((w : PlacesOver L v.1) → (w.1.adicCompletionIntegers L)ˣ)) σ) := fun v ↦ by
    obtain ⟨w⟩ := nonempty_placesOver_of_finite (L := L) v.1
    exact subsingleton_cycTateNegOne_integerUnitsAbove v.1 σ hσ w (hS v.1 v.2 w)
  exact (cycTateNegOneMulPiEquiv
    (fun v : ↥Sᶜ ↦ (w : PlacesOver L v.1) → (w.1.adicCompletionIntegers L)ˣ) σ).toEquiv.subsingleton

theorem cycHerbrand_integerUnitsOutside (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v ∉ S, ∀ w : PlacesOver L v, w.1.asIdeal.ramificationIdx (𝓞 K) = 1)
    (σ : Gal(L/K)) (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    cycHerbrand (Representation.ofMulDistribMulAction Gal(L/K)
      ((v : ↥Sᶜ) → (w : PlacesOver L v.1) → (w.1.adicCompletionIntegers L)ˣ)) σ = 1 := by
  have h0 := subsingleton_cycTateZero_integerUnitsOutside S hS σ hσ
  have h1 := subsingleton_cycTateNegOne_integerUnitsOutside S hS σ hσ
  rw [cycHerbrand_eq, Nat.card_eq_one_iff_unique.2 ⟨h0, ⟨0⟩⟩,
    Nat.card_eq_one_iff_unique.2 ⟨h1, ⟨0⟩⟩]
  norm_num


open AdicLiesOver in
theorem cycHerbrand_sIdeles (S : Set (HeightOneSpectrum (𝓞 K))) (hSf : S.Finite)
    (hS : ∀ v ∉ S, ∀ w : PlacesOver L v, w.1.asIdeal.ramificationIdx (𝓞 K) = 1)
    (σ : Gal(L/K)) (hσ : ∀ g, g ∈ Subgroup.zpowers σ)
    (wInf : ∀ v : InfinitePlace K, v.placesOver L) (wFin : ∀ v : HeightOneSpectrum (𝓞 K), PlacesOver L v) :
    HasHerbrandQuotient
        (cycSubOne (Representation.ofMulDistribMulAction Gal(L/K) (sIdeles (placesAbove L S))) σ)
        (cycNorm (Representation.ofMulDistribMulAction Gal(L/K) (sIdeles (placesAbove L S)))) ∧
      cycHerbrand (Representation.ofMulDistribMulAction Gal(L/K) (sIdeles (placesAbove L S))) σ =
        (∏ v : InfinitePlace K, (Module.finrank v.Completion (wInf v).1.Completion : ℚ)) *
          ∏ v ∈ hSf.toFinset,
            (Module.finrank (v.adicCompletion K) ((wFin v).1.adicCompletion L) : ℚ) := by
  let _ : Fintype S := hSf.fintype
  have key : cycHerbrand (Representation.ofMulDistribMulAction Gal(L/K)
      (sIdeles (placesAbove L S))) σ =
        (∏ v : InfinitePlace K, (Module.finrank v.Completion (wInf v).1.Completion : ℚ)) *
          ∏ v ∈ hSf.toFinset,
            (Module.finrank (v.adicCompletion K) ((wFin v).1.adicCompletion L) : ℚ) := by
    have hcompat : ∀ (g : Gal(L/K)) (x : Additive (sIdeles (placesAbove L S))),
        (sIdelesEquivProduct S hSf).toAdditive
            (Representation.ofMulDistribMulAction Gal(L/K) (sIdeles (placesAbove L S)) g x) =
          Representation.ofMulDistribMulAction Gal(L/K) (SIdelesProduct L S) g
            ((sIdelesEquivProduct S hSf).toAdditive x) := fun g x ↦ by
      apply Additive.toMul.injective
      exact sIdelesEquivProduct_smul S hSf g x.toMul
    rw [cycHerbrand_congr (sIdelesEquivProduct S hSf).toAdditive hcompat σ]
    rw [cycHerbrand_mulProd, cycHerbrand_mulProd, cycHerbrand_integerUnitsOutside S hS σ hσ,
      mul_one, cycHerbrand_mulPi, cycHerbrand_mulPi,
      Finset.prod_subtype hSf.toFinset (fun v ↦ hSf.mem_toFinset)]
    congr 1
    · exact Finset.prod_congr rfl fun v _ ↦ cycHerbrand_infiniteUnitsAbove v σ hσ (wInf v)
    · exact Finset.prod_congr rfl fun v _ ↦ cycHerbrand_finiteUnitsAbove v.1 σ hσ (wFin v.1)
  refine ⟨hasHerbrandQuotient_of_cycHerbrand_ne_zero ?_, key⟩
  rw [key]
  refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun v _ ↦ ?_)
    (Finset.prod_ne_zero_iff.2 fun v _ ↦ ?_)
  · exact Nat.cast_ne_zero.2 (GroundTheory.Global.InfinitePlace.finrank_completion_pos
      (v := v) (wInf v).1).ne'
  · exact Nat.cast_ne_zero.2 Module.finrank_pos.ne'

end IdeleGroup

end

end GroundTheory.Global
end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.GlobalFields.IdeleGroups.SIdeleHerbrand =====
