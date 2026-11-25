module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBidualNaturalityDualSheafTranspose
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToNatLengthEqRangeAddRange
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
public import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasicoherentEigenQuot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVBAndClsDetOfShortExact

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsRetractTensorTriple, Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsEffAddNsmulDiv, Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFrameOfBijectiveStalk, Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoGenResMapSmulHom

-- ===== clump member: Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsRetractTensorTriple =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsRetractTensorTriple", "h": "module\n\npublic import Mathlib.AlgebraicGeometry.Morphisms.Flat\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens\npublic import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp\npublic import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite\npublic import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

noncomputable section

namespace GlobalTheory.Models

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem flat_projSpace (R : Type) [CommRing R] (N : ℕ) : Flat (PSpace.str R N) :=
  haveI : IsZariskiLocalAtSource @Flat.{0} := HasRingHomProperty.instIsZariskiLocalAtSource
  IsZariskiLocalAtSource.of_openCover (P := @Flat) (ProjSpace.chartCover R N) fun (i : Fin (N + 1)) => by
    change Flat (ProjSpace.chartι R N i ≫ _)
    rw [ProjSpace.chartι_str, HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (inferInstanceAs (Module.Flat R (MvPolynomial _ R)))

end GlobalTheory.Models

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsRetractTensorTriple =====

-- ===== clump member: Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsEffAddNsmulDiv =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsEffAddNsmulDiv", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.ToNatLengthEqRangeAddRange\npublic import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsRetractTensorTriple\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint\npublic import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp\npublic import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists\nimport Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver\nimport Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated\nimport Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator\nimport Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.KrullDimension.Polynomial\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.TypeStar\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso\n\n"}
section -- clump:auto
@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace TensorProduct IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.QCoh GlobalTheory.CechPic
open GlobalTheory.LB (resG_resG resG_self val_res toMod coord ofSec)
open GlobalTheory.Cartier (IsRegularFn IsRegularSec SecMaps germ_resG ext_germK)

namespace GlobalTheory.Vert

theorem shortExact_cokernel_comp {C : Type*} [Category C] [Abelian C] {A B E : C} (f : A ⟶ B)
    (g : B ⟶ E) [Mono g] : (kernelCokernelCompSequence.snakeInput f g).L₃.ShortExact := by
  let S := kernelCokernelCompSequence.snakeInput f g
  have : Epi S.L₂.g := inferInstanceAs (Epi (biprod.snd : B ⊞ E ⟶ E))
  exact ShortComplex.ShortExact.mk' S.L₃_exact
    (S.L₂'_exact.mono_g ((isZero_kernel_of_mono g).eq_of_src _ _)) S.epi_L₃_g

section Divisor

variable {X : Scheme.{0}}

variable (D D' : EffCartierData X)

theorem idealSheaf_eq_of_germ
    (h : ∀ (x : X) (i : D.ι) (j : D'.ι) (hi : x ∈ D.U i) (hj : x ∈ D'.U j),
      Associated ((X.presheaf.germ _ x hi).hom (D.f i)) ((X.presheaf.germ _ x hj).hom (D'.f j))) :
    D.idealSheaf = D'.idealSheaf := by
  ext W a
  rw [EffCartierData.idealSheaf, EffCartierData.idealSheaf, EffCartierData.mem_locIdeal_iff,
    EffCartierData.mem_locIdeal_iff]
  refine ⟨fun H j x hx hj => ?_, fun H i x hx hi => ?_⟩
  · obtain ⟨i, hi⟩ := D.exists_mem x
    exact (h x i j hi hj).symm.dvd.trans (H i x hx hi)
  · obtain ⟨j, hj⟩ := D'.exists_mem x
    exact (h x i j hi hj).dvd.trans (H j x hx hj)

theorem germ_add_f (x : X) (p : (D.add D').ι) (h : x ∈ (D.add D').U p) :
    (X.presheaf.germ _ x h).hom ((D.add D').f p) =
      (X.presheaf.germ _ x h.1).hom (D.f p.1) * (X.presheaf.germ _ x h.2).hom (D'.f p.2) :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (germ_resG _ _ _ _) (germ_resG _ _ _ _))

theorem idealSheaf_mul_left_cancel {E D D' : EffCartierData X}
    (h : E.idealSheaf * D.idealSheaf = E.idealSheaf * D'.idealSheaf) :
    D.idealSheaf = D'.idealSheaf := by
  rw [← E.idealSheaf_add, ← E.idealSheaf_add] at h
  refine idealSheaf_eq_of_germ D D' fun x i j hi hj => ?_
  obtain ⟨k, hk⟩ := E.exists_mem x
  obtain ⟨u, hu⟩ := (EffCartierData.associated_of_idealSheaf_eq _ _ h (k, j) (k, i)).map
    (X.presheaf.germ _ x (show x ∈ E.U k ⊓ D'.U j ⊓ (E.U k ⊓ D.U i) from ⟨⟨hk, hj⟩, hk, hi⟩)).hom
  refine ⟨u, (mul_cancel_left_mem_nonZeroDivisors
    (Cartier.isRegularFn_iff_germ.1 (E.regular k) x hk)).1 ?_⟩
  rw [← mul_assoc]
  exact (congrArg (· * _) ((germ_resG _ _ _ _).trans (germ_add_f E D x (k, i) ⟨hk, hi⟩))).symm.trans
    (hu.trans ((germ_resG _ _ _ _).trans (germ_add_f E D' x (k, j) ⟨hk, hj⟩)))

theorem le_basicOpen_of_isUnit {U V : X.Opens} (h : V ≤ U) {a : Γ(X, U)}
    (ha : IsUnit (resG X h a)) : V ≤ X.basicOpen a := by
  rw [← X.basicOpen_of_isUnit ha]
  exact (X.basicOpen_res a (homOfLE h).op).le.trans inf_le_right

end Divisor

variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

structure Model (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] where

  X : Scheme.{0}

  str : X ⟶ Sp O

  [isIntegral : IsIntegral X]

  isProjOver : IsProjOver str

  [flat : Flat str]

attribute [instance] Model.isIntegral Model.flat

theorem topologicalKrullDim_pspace (N : ℕ) :
    topologicalKrullDim (PSpace O N) = (N + 1 : ℕ) := by
  have hc : ∀ i, topologicalKrullDim (ProjSpace.chart O N i : Set (PSpace O N)) = (N + 1 : ℕ) :=
    fun i => by
      rw [topologicalKrullDim_eq_of_isEmbedding (ProjSpace.chartι O N i).isOpenEmbedding.isEmbedding
        (congrArg SetLike.coe (ProjSpace.opensRange_chartι O N i))]
      refine (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim
        (R := MvPolynomial {j // j ≠ i} O)).trans ?_
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, IsDiscreteValuationRing.ringKrullDim_eq_one]
      simp [add_comm]
  refine le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_)
    ((hc 0).ge.trans (topologicalKrullDim_subspace_le _ _))
  obtain ⟨i, hi⟩ := ProjSpace.exists_mem_chart O N x
  exact ⟨_, (ProjSpace.chart O N i).isOpen, hi, (hc i).le⟩

namespace Model

variable {O} (Z Z₁ Z₂ : Model O)

instance algebraTop : Algebra O Γ(Z.X, ⊤) := algebraΓOfHom Z.str

abbrev const (g : O) : Γ(Z.X, ⊤) := algebraMap O Γ(Z.X, ⊤) g

theorem const_eq (g : O) : algebraMap O Γ(Z.X, ⊤) g =
    Z.str.appTop ((Scheme.ΓSpecIso (.of O)).inv g) := rfl

instance isNoetherian : AlgebraicGeometry.IsNoetherian Z.X :=
  isNoetherian_of_isProjOver Z.isProjOver

instance isProper : IsProper Z.str := (isProper_and_exists_isAmpleLB_of_isProjOver Z.isProjOver).1

def gen : Z.X.Opens :=
  Z.str ⁻¹ᵁ ⟨{closedPoint O}ᶜ, (IsLocalRing.isClosed_singleton_closedPoint O).isOpen_compl⟩


variable {Z} in
theorem mem_gen {x : Z.X} : x ∈ Z.gen ↔ Z.str x ≠ closedPoint O := Iff.rfl


variable {Z} in
theorem mem_gen_iff_eq_bot {x : Z.X} : x ∈ Z.gen ↔ (Z.str x).asIdeal = ⊥ := by
  refine ⟨fun h => by_contra fun h' => h (PrimeSpectrum.ext
    (eq_maximalIdeal ((Z.str x).isPrime.isMaximal h'))), fun h h' => ?_⟩
  exact IsDiscreteValuationRing.not_a_field O ((congrArg PrimeSpectrum.asIdeal h').symm.trans h)


variable {Z} in
theorem mem_basicOpen_const {x : Z.X} {g : O} :
    x ∈ Z.X.basicOpen (Z.const g) ↔ g ∉ (Z.str x).asIdeal := by
  rw [const, const_eq, ← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
  rfl

theorem gen_le_basicOpen {g : O} (hg : g ≠ 0) : Z.gen ≤ Z.X.basicOpen (Z.const g) :=
  fun _ hx => mem_basicOpen_const.2 (by rwa [mem_gen_iff_eq_bot.1 hx])

theorem gen_eq_basicOpen {g : O} (hg : g ≠ 0) (hm : g ∈ maximalIdeal O) :
    Z.gen = Z.X.basicOpen (Z.const g) :=
  (Z.gen_le_basicOpen hg).antisymm fun _ hx h => mem_basicOpen_const.1 hx (h ▸ hm)

theorem isUnit_const {g : O} (hg : g ≠ 0) {V : Z.X.Opens} (h : V ≤ Z.gen) :
    IsUnit (resG Z.X (le_top : V ≤ ⊤) (Z.const g)) := by
  rw [← resG_resG (Z.X.basicOpen_le (Z.const g)) (h.trans (Z.gen_le_basicOpen hg))]
  exact (Z.X.toRingedSpace.isUnit_res_basicOpen _).map _

theorem isRegularFn_const {g : O} (hg : g ≠ 0) : IsRegularFn (Z.const g) :=
  (EffCartierData.isRegularFn_spec (mem_nonZeroDivisors_of_ne_zero hg)).app_of_flat Z.str

theorem genericPoint_mem_gen : genericPoint Z.X ∈ Z.gen := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  rw [Z.gen_eq_basicOpen hϖ.ne_zero hϖ.not_isUnit]
  obtain ⟨x, hx⟩ := (Opens.ne_bot_iff_nonempty _).1 (mt (basicOpen_eq_bot_iff _).1
    (Z.isRegularFn_const hϖ.ne_zero).ne_zero)
  exact VB.genericPoint_mem hx

theorem exists_notMem_gen : ∃ x : Z.X, x ∉ Z.gen := by
  obtain ⟨x, hx⟩ := (specializes_closedPoint (Z.str (genericPoint Z.X))).mem_closed
    Z.str.isClosedMap.isClosed_range ⟨_, rfl⟩
  exact ⟨x, fun h => h hx⟩

theorem resG_injective {V W : Z.X.Opens} (h : W ≤ V) (hW : Z.gen ⊓ V ≤ W) :
    Function.Injective (resG Z.X h) := fun _ _ e => ext_germK fun hV => by
  rw [← germ_resG h _ (hW ⟨Z.genericPoint_mem_gen, hV⟩), e, germ_resG]

theorem dim_special_add_one_le :
    topologicalKrullDim ((Z.gen : Set Z.X)ᶜ : Set Z.X) + 1 ≤ topologicalKrullDim Z.X := by
  have := topologicalKrullDim_add_one_le Z.gen.isOpen.isClosed_compl isClosed_univ
    fun x _ => ⟨genericPoint Z.X, trivial, not_not.2 Z.genericPoint_mem_gen,
      genericPoint_specializes x⟩
  rwa [topologicalKrullDim_eq_of_isEmbedding Topology.IsEmbedding.id Set.range_id] at this

theorem exists_dim_eq : ∃ d : ℕ, topologicalKrullDim Z.X = (d + 1 : ℕ) := by
  obtain ⟨N, i, _, -⟩ := Z.isProjOver
  have h₁ := i.isClosedEmbedding.isInducing.topologicalKrullDim_le.trans_eq
    (topologicalKrullDim_pspace O N)
  have h₂ := Z.dim_special_add_one_le
  have h₃ : topologicalKrullDim ((Z.gen : Set Z.X)ᶜ : Set Z.X) ≠ ⊥ :=
    mt topologicalKrullDim_eq_bot_iff.1 (not_isEmpty_iff.2 (nonempty_subtype.2 Z.exists_notMem_gen))
  generalize topologicalKrullDim Z.X = a at *
  generalize topologicalKrullDim ((Z.gen : Set Z.X)ᶜ : Set Z.X) = b at *
  lift b to ℕ∞ using h₃
  have h₄ : (1 : WithBot ℕ∞) ≤ a := le_trans (by exact_mod_cast le_add_self) h₂
  lift a to ℕ∞ using by rintro rfl; simp at h₄
  lift a to ℕ using by rintro rfl; exact absurd h₁ (by exact_mod_cast (ENat.natCast_lt_top _).not_ge)
  have : 1 ≤ a := by exact_mod_cast h₄
  exact ⟨a - 1, by rw [Nat.sub_add_cancel this]; rfl⟩

def relDim : ℕ := Z.exists_dim_eq.choose

theorem dim_eq : topologicalKrullDim Z.X = (Z.relDim + 1 : ℕ) := Z.exists_dim_eq.choose_spec


variable {Z} in
theorem relDim_eq_iff {d : ℕ} : Z.relDim = d ↔ topologicalKrullDim Z.X = (d + 1 : ℕ) := by
  rw [dim_eq]
  exact ⟨fun h => h ▸ rfl, fun h => Nat.succ_injective (by exact_mod_cast h)⟩


variable (O) in
def projSpace (N : ℕ) : Model O where
  X := PSpace O N
  str := PSpace.str O N
  isIntegral := ProjSpace.isIntegral_of_isDomain O N
  isProjOver := ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩
  flat := Models.flat_projSpace O N

@[simp] theorem relDim_projSpace (N : ℕ) : (projSpace O N).relDim = N :=
  relDim_eq_iff.2 (topologicalKrullDim_pspace O N)

structure Hom (Z₁ Z : Model O) where

  f : Z₁.X ⟶ Z.X

  comp_str : f ≫ Z.str = Z₁.str

  [surjective : Surjective f]

attribute [instance] Hom.surjective

section Over

variable {Z Z₁} {f : Z₁.X ⟶ Z.X} (hf : f ≫ Z.str = Z₁.str)
include hf

theorem isProper_of_comp_str : IsProper f :=
  have : IsProper (f ≫ Z.str) := hf ▸ Z₁.isProper
  .of_comp f Z.str

theorem preimage_gen : f ⁻¹ᵁ Z.gen = Z₁.gen := by
  rw [gen, ← Scheme.Hom.comp_preimage, hf]; rfl

theorem appTop_const (g : O) : f.appTop (Z.const g) = Z₁.const g := by
  rw [const, const, const_eq, const_eq, ← hf, Scheme.Hom.comp_appTop]; rfl

end Over

end Model

namespace Model

variable {O} (Z Z₁ : Model O)

def effVert : Submonoid Z.X.IdealSheafData where
  carrier := {I | FinalTheorems.EffCartier I ∧ ∀ x ∈ I.support, x ∉ Z.gen}
  one_mem' := ⟨(EffCartierData.idealSheaf_zero (X := Z.X)).subst
    (EffCartierData.zero _).effCartier_idealSheaf, fun x hx => by
      rw [Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.support_top] at hx
      exact hx.elim⟩
  mul_mem' := fun {I J} hI hJ => by
    obtain ⟨D, rfl⟩ := EffCartierData.exists_idealSheaf_eq hI.1
    obtain ⟨D', rfl⟩ := EffCartierData.exists_idealSheaf_eq hJ.1
    exact ⟨D.idealSheaf_add D' ▸ (D.add D').effCartier_idealSheaf,
      fun x hx => Or.elim hx (hI.2 x) (hJ.2 x)⟩

variable {Z}

def effData (I : Z.effVert) : EffCartierData Z.X :=
  (EffCartierData.exists_idealSheaf_eq I.2.1).choose

@[simp] theorem idealSheaf_effData (I : Z.effVert) : (effData I).idealSheaf = I.1 :=
  (EffCartierData.exists_idealSheaf_eq I.2.1).choose_spec

def effMk (D : EffCartierData Z.X) (h : ∀ i, Z.gen ⊓ D.U i ≤ Z.X.basicOpen (D.f i)) : Z.effVert :=
  ⟨D.idealSheaf, D.effCartier_idealSheaf, fun x hx hg =>
    have ⟨i, hi⟩ := D.exists_mem x
    (D.mem_support_iff i hi).1 hx (h i ⟨hg, hi⟩)⟩

theorem le_basicOpen_effData (I : Z.effVert) (i : (effData I).ι) :
    Z.gen ⊓ (effData I).U i ≤ Z.X.basicOpen ((effData I).f i) := fun x hx =>
  by_contra fun h => I.2.2 x (idealSheaf_effData I ▸ ((effData I).mem_support_iff i hx.2).2 h) hx.1

instance : IsCancelMul Z.effVert :=
  have : IsLeftCancelMul Z.effVert := ⟨fun E D D' h => Subtype.ext <| by
    rw [← idealSheaf_effData, ← idealSheaf_effData]
    refine idealSheaf_mul_left_cancel (E := effData E) ?_
    simp only [idealSheaf_effData]
    exact congrArg Subtype.val h⟩
  CommMagma.IsLeftCancelMul.toIsCancelMul _

def effCls (I : Z.effVert) : Pic Z.X := cls _ (effData I).isLB_lb

theorem effCls_eq {I : Z.effVert} {D : EffCartierData Z.X} (h : D.idealSheaf = I.1) :
    effCls I = cls _ D.isLB_lb :=
  (cls_eq_iff _ _).2 (EffCartierData.lbIso_of_idealSheaf_eq _ _ ((idealSheaf_effData I).trans h.symm))

theorem effCls_mul (I J : Z.effVert) : effCls (I * J) = effCls I + effCls J := by
  have h := (cls_eq_iff (effData J).isLB_lb (Semi.LB.isLB_div ((effData I).add (effData J)).isLB_lb
    (effData I).isLB_lb)).2 ((effData I).lbIso_add (effData J))
  rw [cls_div ((effData I).add (effData J)).isLB_lb (effData I).isLB_lb] at h
  rw [effCls_eq (D := (effData I).add (effData J)) (by simp [EffCartierData.idealSheaf_add]),
    effCls, effCls, h, add_sub_cancel]


variable (Z) in
abbrev VDivZ : Type := Algebra.GrothendieckAddGroup (Additive Z.effVert)

def ofEff (I : Z.effVert) : Z.VDivZ := Algebra.GrothendieckAddGroup.of (Additive.ofMul I)

theorem ofEff_mul (I J : Z.effVert) : ofEff (I * J) = ofEff I + ofEff J :=
  map_add Algebra.GrothendieckAddGroup.of (Additive.ofMul I) (Additive.ofMul J)

@[simp] theorem ofEff_one : ofEff (1 : Z.effVert) = 0 := map_zero Algebra.GrothendieckAddGroup.of

theorem ofEff_injective : Function.Injective (ofEff (Z := Z)) :=
  Algebra.GrothendieckAddGroup.of_injective (M := Additive Z.effVert)

def vLift {A : Type*} [AddCommGroup A] (f : Z.effVert → A) (h : ∀ I J, f (I * J) = f I + f J) :
    Z.VDivZ →+ A :=
  Algebra.GrothendieckAddGroup.lift (AddMonoidHom.mk' (fun I => f I.toMul) h)

@[simp] theorem vLift_ofEff {A : Type*} [AddCommGroup A] (f : Z.effVert → A)
    (h : ∀ I J, f (I * J) = f I + f J) (I : Z.effVert) : vLift f h (ofEff I) = f I :=
  DFunLike.congr_fun (Algebra.GrothendieckAddGroup.lift.symm_apply_apply
    (AddMonoidHom.mk' (fun I : Additive Z.effVert => f I.toMul) h)) (Additive.ofMul I)

variable (Z)

def vCls : Z.VDivZ →+ Pic Z.X := vLift effCls effCls_mul


variable {Z} in
@[simp] theorem vCls_ofEff (I : Z.effVert) : Z.vCls (ofEff I) = effCls I := vLift_ofEff _ _ I


def effConst (g : O) (hg : g ≠ 0) : Z.effVert :=
  effMk (.principal (Z.const g) (Z.isRegularFn_const hg))
    fun _ => inf_le_left.trans (Z.gen_le_basicOpen hg)

def div (g : O) (hg : g ≠ 0) : Z.VDivZ := ofEff (Z.effConst g hg)

theorem div_mul {g g' : O} (hg : g ≠ 0) (hg' : g' ≠ 0) (h : g * g' ≠ 0) :
    Z.div (g * g') h = Z.div g hg + Z.div g' hg' := by
  rw [div, div, div, ← ofEff_mul]
  refine congrArg ofEff (Subtype.ext ((idealSheaf_eq_of_germ _ _ fun x i j hi hj => ?_).trans
    (EffCartierData.idealSheaf_add _ _)))
  rw [germ_add_f]
  exact Associated.of_eq ((congrArg _ (map_mul _ g g')).trans (map_mul _ _ _))

theorem div_of_isUnit {g : O} (h : IsUnit g) (hg : g ≠ 0) : Z.div g hg = 0 := by
  rw [← ofEff_one]
  refine congrArg ofEff (Subtype.ext ((idealSheaf_eq_of_germ _ _ fun x i j hi hj => ?_).trans
    EffCartierData.idealSheaf_zero))
  exact (associated_one_iff_isUnit.2 (h.map (algebraMap O Γ(Z.X, ⊤)))).map _

theorem div_pow {g : O} (hg : g ≠ 0) (n : ℕ) (h : g ^ n ≠ 0) :
    Z.div (g ^ n) h = n • Z.div g hg := by
  induction n with
  | zero => simpa using Z.div_of_isUnit isUnit_one _
  | succ n ih => simp only [pow_succ, succ_nsmul, Z.div_mul (pow_ne_zero n hg) hg, ih]

@[simp] theorem vCls_div (g : O) (hg : g ≠ 0) : Z.vCls (Z.div g hg) = 0 := by
  rw [div, vCls_ofEff, effCls_eq (D := .principal (Z.const g) (Z.isRegularFn_const hg)) rfl]
  simp only [EffCartierData.lb_principal]
  rfl

section Pull

variable {Z Z₁} {f : Z₁.X ⟶ Z.X} (hf : f ≫ Z.str = Z₁.str)
include hf

theorem keepsRegular {I : Z.effVert} {D : EffCartierData Z.X} (h : D.idealSheaf = I.1) :
    D.KeepsRegular f :=
  D.keepsRegular_of_notMem_support f (y := genericPoint Z₁.X) fun hx =>
    I.2.2 _ (h ▸ hx) ((preimage_gen hf).ge Z₁.genericPoint_mem_gen)

def effPull (I : Z.effVert) : Z₁.effVert :=
  ⟨I.1.comap f, idealSheaf_effData I ▸ ((effData I).keepsRegular_iff_effCartier f).1
    (keepsRegular hf (idealSheaf_effData I)), fun x hx h => by
      rw [Scheme.IdealSheafData.support_comap] at hx
      exact I.2.2 _ hx ((preimage_gen hf).ge h)⟩

theorem effPull_mul (I J : Z.effVert) : effPull hf (I * J) = effPull hf I * effPull hf J := by
  refine Subtype.ext ?_
  have hI := keepsRegular hf (idealSheaf_effData I)
  have hJ := keepsRegular hf (idealSheaf_effData J)
  change (I.1 * J.1).comap f = I.1.comap f * J.1.comap f
  rw [← idealSheaf_effData I, ← idealSheaf_effData J, ← EffCartierData.idealSheaf_add,
    ← EffCartierData.idealSheaf_pull _ f (hI.add hJ), EffCartierData.pull_add _ _ f hI hJ,
    EffCartierData.idealSheaf_add, EffCartierData.idealSheaf_pull, EffCartierData.idealSheaf_pull]

def vPull : Z.VDivZ →+ Z₁.VDivZ :=
  vLift (fun I => ofEff (effPull hf I)) fun I J => by rw [effPull_mul, ofEff_mul]

@[simp] theorem vPull_ofEff (I : Z.effVert) : vPull hf (ofEff I) = ofEff (effPull hf I) :=
  vLift_ofEff _ _ I

@[simp] theorem vPull_div (g : O) (hg : g ≠ 0) : vPull hf (Z.div g hg) = Z₁.div g hg := by
  rw [div, vPull_ofEff]
  refine congrArg ofEff (Subtype.ext ((EffCartierData.idealSheaf_pull _ f
    (keepsRegular hf (I := Z.effConst g hg) rfl)).symm.trans
      (idealSheaf_eq_of_germ _ _ fun x i j hi hj => ?_)))
  exact Associated.of_eq (congrArg _ (appTop_const hf g))

end Pull

end Model


variable {O} in
structure VertDiv (Z : Model O) where

  M : LB Z.X

  isLB : M.IsLB

  t : Γ(toMod M, Z.gen)

  isUnit : ∀ i, IsUnit (coord t i)

namespace VertDiv

open Model

variable {O} {Z : Model O} (P P' P'' : VertDiv Z)

def eqn (i : P.M.ι) {W : Z.X.Opens} (h : W ≤ Z.gen ⊓ P.M.U i) : Γ(Z.X, W) :=
  resG Z.X h (coord P.t i)

theorem isUnit_eqn (i : P.M.ι) {W : Z.X.Opens} (h : W ≤ Z.gen ⊓ P.M.U i) : IsUnit (P.eqn i h) :=
  (P.isUnit i).map _

@[simp] theorem resG_eqn (i : P.M.ι) {W W' : Z.X.Opens} (h : W ≤ Z.gen ⊓ P.M.U i) (h' : W' ≤ W) :
    resG Z.X h' (P.eqn i h) = P.eqn i (h'.trans h) := resG_resG _ _ _

theorem eqn_rel (i j : P.M.ι) {W : Z.X.Opens} (hi : W ≤ Z.gen ⊓ P.M.U i)
    (hj : W ≤ Z.gen ⊓ P.M.U j) (hij : W ≤ P.M.U i ⊓ P.M.U j) :
    P.eqn i hi = resG Z.X hij (P.M.g i j : Γ(Z.X, P.M.U i ⊓ P.M.U j)) * P.eqn j hj :=
  LB.coord_rel P.t i j hi hj hij

theorem eqn_mul_rel (i j : P.M.ι) (i' j' : P'.M.ι) {W V : Z.X.Opens} (hi : W ≤ Z.gen ⊓ P.M.U i)
    (hj : W ≤ Z.gen ⊓ P.M.U j) (hi' : W ≤ Z.gen ⊓ P'.M.U i') (hj' : W ≤ Z.gen ⊓ P'.M.U j')
    (h : W ≤ V) (hij : V ≤ P.M.U i ⊓ P.M.U j) (hij' : V ≤ P'.M.U i' ⊓ P'.M.U j') :
    P.eqn i hi * P'.eqn i' hi' =
      resG Z.X h (res hij (P.M.g i j) * res hij' (P'.M.g i' j')).val *
        (P.eqn j hj * P'.eqn j' hj') := by
  rw [P.eqn_rel i j hi hj (h.trans hij), P'.eqn_rel i' j' hi' hj' (h.trans hij'), mul_mul_mul_comm,
    Units.val_mul, map_mul, val_res, val_res, resG_resG, resG_resG]

def ofUnits (M : LB Z.X) (hM : M.IsLB) (u : ∀ i, Γ(Z.X, Z.gen ⊓ M.U i))
    (hu : ∀ i, IsUnit (u i)) (h : u ∈ secOn M Z.gen) : VertDiv Z :=
  ⟨M, hM, LB.mkSec u h, hu⟩


variable (Z) in
def zero : VertDiv Z :=
  ofUnits (LB.triv _) (LB.isLB_triv _) (fun _ => 1) (fun _ => isUnit_one) fun _ _ => by
    change _ = resG Z.X _ 1 * _
    simp only [map_one, mul_one]


variable (Z) in
def const (g : O) (hg : g ≠ 0) : VertDiv Z :=
  ofUnits (LB.triv _) (LB.isLB_triv _) (fun _ => resG Z.X le_top (Z.const g))
    (fun _ => Z.isUnit_const hg inf_le_left) fun _ _ => by
      change _ = resG Z.X _ 1 * _
      simp only [map_one, one_mul, resG_resG]

def add : VertDiv Z :=
  ofUnits (tens P.M P'.M) (isLB_tens P.isLB P'.isLB)
    (fun p => P.eqn p.1 (inf_le_inf_left _ inf_le_left) * P'.eqn p.2 (inf_le_inf_left _ inf_le_right))
    (fun _ => (P.isUnit_eqn _ _).mul (P'.isUnit_eqn _ _)) fun p q => by
      simp only [map_mul, resG_eqn]
      exact eqn_mul_rel P P' p.1 q.1 p.2 q.2 _ _ _ _ _ _ _

def ofEff (I : Z.effVert) : VertDiv Z :=
  ⟨(effData I).lb, (effData I).isLB_lb, ofSec (effData I).canonical _, fun i => by
    refine (resG_resG (Z.X.basicOpen_le ((effData I).f i)) (le_basicOpen_effData I i) _).subst ?_
    exact (Z.X.toRingedSpace.isUnit_res_basicOpen _).map _⟩

def IsIsom : Prop := ∃ w : LB.Iso P.M P'.M, w.IsGen ∧ ∀ (p : P'.M.ι) (q : P.M.ι),
  P'.eqn p (inf_le_inf_left _ inf_le_left : Z.gen ⊓ (P'.M.U p ⊓ P.M.U q) ≤ _) =
    resG Z.X inf_le_right (Twist.isoUnit w p q : Γ(Z.X, P'.M.U p ⊓ P.M.U q)) *
      P.eqn q (inf_le_inf_left _ inf_le_right)

def Extends (g : O) (s : P.M.Sec) : Prop :=
  ofSec s Z.gen = resG Z.X (le_top : Z.gen ≤ ⊤) (Z.const g) • P.t

variable {P P' P''} {g g' g'' : O} {s : P.M.Sec} {s' : P'.M.Sec} {s'' : P''.M.Sec}

theorem Extends.resG_f (h : P.Extends g s) (i : P.M.ι) {W : Z.X.Opens}
    (hW : W ≤ Z.gen ⊓ P.M.U i) :
    resG Z.X (hW.trans inf_le_right) (s.f i) = resG Z.X le_top (Z.const g) * P.eqn i hW := by
  have := congrArg (fun t => resG Z.X hW (coord t i)) h
  simpa only [LB.coord_ofSec, LB.coord_smul, map_mul, resG_resG, eqn] using this

theorem Extends.le_basicOpen (h : P.Extends g s) (hg : g ≠ 0) (i : P.M.ι) :
    Z.gen ⊓ P.M.U i ≤ Z.X.basicOpen (s.f i) :=
  le_basicOpen_of_isUnit inf_le_right
    (h.resG_f i le_rfl ▸ (Z.isUnit_const hg inf_le_left).mul (P.isUnit_eqn i _))

theorem Extends.isRegularSec (h : P.Extends g s) (hg : g ≠ 0) : IsRegularSec s :=
  Cartier.isRegularSec_of_ne_zero s (i := Cartier.genericChart P.isLB) fun e => by
    simpa [e] using h.le_basicOpen hg _ ⟨Z.genericPoint_mem_gen, Cartier.mem_genericChart P.isLB⟩

def Extends.eff (h : P.Extends g s) (hg : g ≠ 0) : Z.effVert :=
  effMk (.ofSec P.isLB s (h.isRegularSec hg)) (h.le_basicOpen hg)

theorem Extends.smul (h : P.Extends g s) (g' : O) : P.Extends (g' * g) (Z.const g' • s) :=
  LB.sec_ext fun i => by
    have := h.resG_f i le_rfl
    simp only [LB.coord_ofSec, LB.coord_smul, LB.smul_f, map_mul, resG_resG, this, eqn, resG_self,
      mul_assoc]


variable (P) in
theorem exists_extends {a : O} (ha : a ≠ 0) (hm : a ∈ maximalIdeal O) :
    ∃ (m : ℕ) (s : P.M.Sec), P.Extends (a ^ m) s := by
  have := LB.isQuasicoherent_toMod P.isLB
  obtain ⟨m, t, ht⟩ := Qcqs.exists_pow_smul_eq_res_of_qcqs (toMod P.M) (U := ⊤) isCompact_univ
    isQuasiSeparated_univ (Z.const a) le_top (Z.gen_eq_basicOpen ha hm) P.t
  refine ⟨m, LB.globalEquiv _ t, ?_⟩
  rw [Extends, ← LB.map_ofSec _ (le_top : Z.gen ≤ ⊤), ← LB.globalEquiv_symm_apply,
    LinearEquiv.symm_apply_apply, ← ht]
  simp only [Model.const, map_pow]


variable (P P' P'') in
def IsSum : Prop := ∀ (i : P.M.ι) (j : P'.M.ι) (k : P''.M.ι),
  ∃ u : Γ(Z.X, P.M.U i ⊓ P'.M.U j ⊓ P''.M.U k)ˣ,
    P''.eqn k (inf_le_inf_left _ inf_le_right : Z.gen ⊓ (P.M.U i ⊓ P'.M.U j ⊓ P''.M.U k) ≤ _) =
      resG Z.X inf_le_right u * (P.eqn i (inf_le_inf_left _ (inf_le_left.trans inf_le_left)) *
        P'.eqn j (inf_le_inf_left _ (inf_le_left.trans inf_le_right)))

theorem IsSum.ofEff_sub (H : IsSum P P' P'') (h : P.Extends g s) (h' : P'.Extends g' s')
    (h'' : P''.Extends g'' s'') (hg : g ≠ 0) (hg' : g' ≠ 0) (hg'' : g'' ≠ 0) :
    Model.ofEff (h''.eff hg'') - Z.div g'' hg'' =
      (Model.ofEff (h.eff hg) - Z.div g hg) + (Model.ofEff (h'.eff hg') - Z.div g' hg') := by
  suffices e : h''.eff hg'' * Z.effConst g hg * Z.effConst g' hg' =
      h.eff hg * h'.eff hg' * Z.effConst g'' hg'' by
    have := congrArg Model.ofEff e
    simp only [ofEff_mul] at this
    simp only [div]
    rw [sub_add_sub_comm, sub_eq_sub_iff_add_eq_add, ← add_assoc, this]
  refine Subtype.ext ?_
  simp only [Submonoid.coe_mul, Extends.eff, effConst, effMk, ← EffCartierData.idealSheaf_add]
  refine idealSheaf_eq_of_germ _ _ fun x k p hk hp => ?_
  simp only [germ_add_f]
  obtain ⟨u, hu⟩ := H p.1.1 p.1.2 k.1.1
  have e : resG Z.X (inf_le_right : P.M.U p.1.1 ⊓ P'.M.U p.1.2 ⊓ P''.M.U k.1.1 ≤ _)
      (s''.f k.1.1) * resG Z.X le_top (Z.const g) *
      resG Z.X le_top (Z.const g') = u.val * (resG Z.X (inf_le_left.trans inf_le_left) (s.f p.1.1) *
        resG Z.X (inf_le_left.trans inf_le_right) (s'.f p.1.2) * resG Z.X le_top (Z.const g'')) := by
    refine Z.resG_injective inf_le_right le_rfl ?_
    simp only [map_mul, resG_resG]
    rw [h''.resG_f _ (inf_le_inf_left _ inf_le_right), hu,
      h.resG_f _ (inf_le_inf_left _ (inf_le_left.trans inf_le_left)),
      h'.resG_f _ (inf_le_inf_left _ (inf_le_left.trans inf_le_right))]
    ring
  have e' := congrArg (Z.X.presheaf.germ _ x (show x ∈ P.M.U p.1.1 ⊓ P'.M.U p.1.2 ⊓ P''.M.U k.1.1
    from ⟨⟨hp.1.1, hp.1.2⟩, hk.1.1⟩)).hom e
  simp only [map_mul, germ_resG] at e'
  exact (Associated.of_eq e').trans (associated_unit_mul_left _ _ (u.isUnit.map _))


variable (P) in
theorem exists_extends' : ∃ q : {g : O // g ≠ 0} × P.M.Sec, P.Extends q.1 q.2 :=
  have ⟨_, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have ⟨m, s, h⟩ := P.exists_extends hϖ.ne_zero hϖ.not_isUnit
  ⟨⟨⟨_, pow_ne_zero m hϖ.ne_zero⟩, s⟩, h⟩


variable (P) in
def cls : Z.VDivZ :=
  Model.ofEff (P.exists_extends'.choose_spec.eff P.exists_extends'.choose.1.2) -
    Z.div _ P.exists_extends'.choose.1.2

theorem IsSum.cls_eq (H : IsSum P P' P'') : P''.cls = P.cls + P'.cls := H.ofEff_sub _ _ _ _ _ _

theorem IsIsom.isSum (H : IsIsom P P') : IsSum P (zero Z) P' := fun i _ k => by
  obtain ⟨w, -, hw⟩ := H
  refine ⟨res (le_inf inf_le_right (inf_le_left.trans inf_le_left)) (Twist.isoUnit w k i), ?_⟩
  have := congrArg (resG Z.X (inf_le_inf_left _ (le_inf inf_le_right
    (inf_le_left.trans inf_le_left)) : Z.gen ⊓ (P.M.U i ⊓ ⊤ ⊓ P'.M.U k) ≤ _)) (hw k i)
  simp only [map_mul, resG_eqn, resG_resG] at this
  refine this.trans (congrArg₂ (· * ·) (resG_resG _ _ _).symm ?_)
  exact (mul_one _).symm.trans (congrArg _ (map_one _).symm)


variable (P) in
theorem IsIsom.refl : IsIsom P P :=
  ⟨idIso P.M, idIso_isGen P.isLB, fun p q => P.eqn_rel p q _ _ _⟩


variable (Z) in
@[simp] theorem cls_zero : (zero Z).cls = 0 := by simpa using (IsIsom.refl (zero Z)).isSum.cls_eq

theorem Extends.cls_eq (h : P.Extends g s) (hg : g ≠ 0) :
    P.cls = Model.ofEff (h.eff hg) - Z.div g hg :=
  ((IsIsom.refl P).isSum.ofEff_sub h _ _ hg _ _).trans
    ((congrArg _ (cls_zero Z)).trans (add_zero _))

theorem IsIsom.cls_eq (H : IsIsom P P') : P.cls = P'.cls := by simpa using H.isSum.cls_eq.symm



theorem extends_one (h : ofSec s Z.gen = P.t) : P.Extends 1 s := by
  rw [Extends, Model.const, map_one, map_one, one_smul, h]

theorem Extends.cls_eq_ofEff (h : P.Extends 1 s) : P.cls = Model.ofEff (h.eff one_ne_zero) := by
  rw [h.cls_eq one_ne_zero, Z.div_of_isUnit isUnit_one, sub_zero]


variable (Z) in
@[simp] theorem cls_const (g : O) (hg : g ≠ 0) : (const Z g hg).cls = Z.div g hg := by
  have h : (const Z g hg).Extends 1 ⟨fun _ => Z.const g, fun _ _ => (one_mul _).symm⟩ :=
    extends_one rfl
  exact h.cls_eq_ofEff


variable (P) in
@[simp] theorem vCls_cls : Z.vCls P.cls = CechPic.cls P.M P.isLB := by
  rw [cls, map_sub, vCls_div, sub_zero, vCls_ofEff, effCls_eq rfl, cls_eq_iff]
  exact EffCartierData.lbIso_ofSec _ _ _

theorem cls_eq_iff : P.cls = P'.cls ↔ IsIsom P P' := by
  refine ⟨fun e => ?_, IsIsom.cls_eq⟩
  obtain ⟨⟨⟨g, hg⟩, s⟩, h⟩ := P.exists_extends'
  obtain ⟨⟨⟨g', hg'⟩, s'⟩, h'⟩ := P'.exists_extends'
  have h₁ := h.smul g'
  have h₂ := mul_comm g g' ▸ h'.smul g
  have h0 := mul_ne_zero hg' hg
  rw [h₁.cls_eq h0, h₂.cls_eq h0, sub_left_inj] at e
  have e' := congrArg Subtype.val (ofEff_injective e)
  obtain ⟨w, hw, -⟩ := Cartier.existsUnique_secMaps (b := Z.const g • s') (h₁.isRegularSec h0)
    (EffCartierData.associated_of_idealSheaf_eq _ _ e')
  refine ⟨w, hw.1, fun p q => (Z.isUnit_const h0 inf_le_left).mul_left_cancel ?_⟩
  rw [← h₂.resG_f, mul_left_comm, ← h₁.resG_f, hw.2.on p q]
  rfl

section Pull

variable {Z₁ : Model O} {f : Z₁.X ⟶ Z.X} (hf : f ≫ Z.str = Z₁.str)



end Pull

end VertDiv

end GlobalTheory.Vert
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsEffAddNsmulDiv =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFrameOfBijectiveStalk =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFrameOfBijectiveStalk", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.ToBidualNaturalityDualSheafTranspose\nimport Mathlib.Algebra.Module.StablyFree.Basic\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (resG_resG)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM germ_resM)
open GlobalTheory.QCoh (appLinear appLinear_apply stalkLinear)

namespace GlobalTheory.VB.Ker

section Algebra

variable {R M₁ M₂ M₃ : Type} [CommRing R] [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
  [Module R M₁] [Module R M₂] [Module R M₃] {f : M₁ →ₗ[R] M₂} {g : M₂ →ₗ[R] M₃}

theorem bijective_sumElim_iff {ι κ : Type} [Fintype ι] [Fintype κ] (hf : Function.Injective f)
    (hfg : Function.Exact f g) (e : ι → M₁) (t : κ → M₂)
    (ht : Function.Bijective (Fintype.linearCombination R fun j => g (t j))) :
    Function.Bijective (Fintype.linearCombination R (Sum.elim (fun i => f (e i)) t)) ↔
      Function.Bijective (Fintype.linearCombination R e) := by
  have h1 (a : ι ⊕ κ → R) : Fintype.linearCombination R (Sum.elim (fun i => f (e i)) t) a =
      f (Fintype.linearCombination R e fun i => a (.inl i)) +
        Fintype.linearCombination R t fun j => a (.inr j) := by

    simp [Fintype.linearCombination_apply, Fintype.sum_sum_type, map_sum]
  have h2 (b : κ → R) : g (Fintype.linearCombination R t b) =
      Fintype.linearCombination R (fun j => g (t j)) b := by

    simp [Fintype.linearCombination_apply, map_sum]
  have h3 (b : κ → R) (m m' : M₁) (h : f m + Fintype.linearCombination R t b = f m') : b = 0 := by
    have := congrArg g h
    rw [map_add (f := _), hfg.apply_apply_eq_zero, hfg.apply_apply_eq_zero, zero_add, h2] at this
    exact ht.1 (this.trans (map_zero _).symm)
  constructor
  · refine fun H => ⟨(injective_iff_map_eq_zero _).2 fun a ha => ?_, fun m => ?_⟩
    · have : Sum.elim a (0 : κ → R) = 0 := H.1 (by
        rw [h1, map_zero]
        change f (Fintype.linearCombination R e a) + Fintype.linearCombination R t 0 = 0
        rw [ha, map_zero, map_zero, add_zero])
      exact funext fun i => congrFun this (.inl i)
    · obtain ⟨a, ha⟩ := H.2 (f m)
      rw [h1] at ha
      rw [h3 _ _ _ ha, map_zero, add_zero] at ha
      exact ⟨_, hf ha⟩
  · refine fun H => ⟨(injective_iff_map_eq_zero _).2 fun a ha => ?_, fun m => ?_⟩
    · rw [h1, ← map_zero f] at ha
      have hb := h3 _ _ _ ha
      rw [hb, map_zero, add_zero] at ha
      have ha' := H.1 ((hf ha).trans (map_zero _).symm)
      funext k
      rcases k with i | j
      exacts [congrFun ha' i, congrFun hb j]
    · obtain ⟨b, hb⟩ := ht.2 (g m)
      obtain ⟨n, hn⟩ := (hfg (m - Fintype.linearCombination R t b)).1 (by
        rw [map_sub, h2, hb, sub_self])
      obtain ⟨a, rfl⟩ := H.2 n
      exact ⟨Sum.elim a b, by rw [h1]; exact eq_sub_iff_add_eq.1 hn⟩

theorem nonempty_basis_of_exact [IsLocalRing R] {r s : ℕ} (hf : Function.Injective f)
    (hfg : Function.Exact f g) (hg : Function.Surjective g) (b : Module.Basis (Fin (r + s)) R M₂)
    (c : Module.Basis (Fin s) R M₃) : Nonempty (Module.Basis (Fin r) R M₁) := by
  have := Module.Free.of_basis b
  have := Module.Free.of_basis c
  have := Module.Finite.of_basis b
  have := Module.Finite.of_basis c
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property g LinearMap.id hg
  obtain ⟨φ, hφ, -⟩ := hfg.splitSurjectiveEquiv hf ⟨σ, hσ⟩
  let π : M₂ →ₗ[R] M₁ := LinearMap.fst R M₁ M₃ ∘ₗ φ.toLinearMap
  have hπ : π ∘ₗ f = LinearMap.id := by
    ext m
    simp [π, hφ]
  have : Module.Projective R M₁ := .of_split f π hπ
  have : Module.Finite R M₁ := .of_surjective π fun m => ⟨f m, LinearMap.congr_fun hπ m⟩
  have : Module.Free R M₁ := Module.free_of_flat_of_isLocalRing
  have h := φ.finrank_eq
  rw [Module.finrank_prod, Module.finrank_eq_card_basis b, Module.finrank_eq_card_basis c,
    Fintype.card_fin, Fintype.card_fin] at h
  exact ⟨Module.finBasisOfFinrankEq R M₁ (by omega)⟩

theorem bijective_iff_isUnit_det {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R M₁)
    (v : ι → M₁) : Function.Bijective (Fintype.linearCombination R v) ↔ IsUnit (b.det v) := by
  rw [← Module.Basis.is_basis_iff_det, Function.Bijective, ← linearIndependent_iff_injective_fintypeLinearCombination,
    ← LinearMap.range_eq_top, Fintype.range_linearCombination]

end Algebra

variable {X : Scheme.{0}} {F : X.Modules} {U : X.Opens} {ι : Type} [Fintype ι]

theorem exists_germ_eq_family {x : X} (hx : x ∈ U) (a : ι → (F.presheaf.stalk x :)) :
    ∃ (V : X.Opens) (_ : V ≤ U) (hV : x ∈ V) (e : ι → Γ(F, V)),
      ∀ i, F.presheaf.germ V x hV (e i) = a i := by
  choose W hW b hb using fun i => F.presheaf.exists_germ_eq (a i)
  have hxV : x ∈ U ⊓ Finset.univ.inf W := ⟨hx, by
    rw [Opens.coe_finset_inf]; simpa using hW⟩
  have hV (i : ι) : U ⊓ Finset.univ.inf W ≤ W i :=
    inf_le_right.trans (Finset.inf_le (Finset.mem_univ i))
  exact ⟨_, inf_le_left, hxV, fun i => resM F (hV i) (b i), fun i => by rw [germ_resM, hb]⟩

theorem germ_det [DecidableEq ι] {e : ι → Γ(F, U)} (he : IsFrame e) (v : ι → Γ(F, U)) {x : X}
    (hx : x ∈ U) : X.presheaf.germ U x hx ((he.basis le_rfl).det v) =
      (he.stalkBasis x hx).det fun i => F.presheaf.germ U x hx (v i) := by
  rw [Module.Basis.det_apply, Module.Basis.det_apply]
  refine (RingHom.map_det (X.presheaf.germ U x hx).hom _).trans ?_
  congr 1
  ext i j
  rw [Module.Basis.toMatrix_apply]
  conv_rhs => rw [← (he.basis le_rfl).sum_repr (v j)]

  simp only [map_sum, QCoh.germ_smul, IsFrame.basis_apply, resM_self]
  simp only [← he.stalkBasis_apply x hx]

  rw [← map_sum, Module.Basis.repr_sum_self]
  rfl

theorem exists_isFrame_of_bijective_stalk {e : ι → Γ(F, U)} (he : IsFrame e) (v : ι → Γ(F, U))
    {x : X} (hx : x ∈ U) (hv : Function.Bijective (Fintype.linearCombination (X.presheaf.stalk x)
      fun i => (F.presheaf.germ U x hx (v i) : (F.presheaf.stalk x :)))) :
    ∃ (W : X.Opens) (h : W ≤ U), x ∈ W ∧ IsFrame fun i => resM F h (v i) := by
  classical
  rw [bijective_iff_isUnit_det (he.stalkBasis x hx), ← germ_det he] at hv
  refine ⟨X.basicOpen ((he.basis le_rfl).det v), X.basicOpen_le _,
    (X.mem_basicOpen _ x hx).2 hv, fun V h => ?_⟩
  simp only [resM_resM]
  rw [bijective_iff_isUnit_det (he.basis ((h.trans (X.basicOpen_le _)).trans le_rfl)),
    ← he.resG_det, ← resG_resG (X.basicOpen_le _) h]
  exact (X.toRingedSpace.isUnit_res_basicOpen _).map _

end GlobalTheory.VB.Ker

namespace GlobalTheory.VB

open Ker

theorem isVB_X₁_of_shortExact : ∀ (X : Scheme.{0}) (S : ShortComplex X.Modules) (r s : ℕ),
    S.ShortExact → IsVB S.X₂ (r + s) → IsVB S.X₃ s → IsVB S.X₁ r := by
  intro X S r s hS h₂ h₃ x
  have := hS.mono_f
  have := hS.epi_g
  have := h₂.isQuasicoherent
  have := h₃.isQuasicoherent
  obtain ⟨U₀, b₀, hx₀, hb₀⟩ := h₂ x
  obtain ⟨U, c, hU, hx, hle, hc⟩ := h₃.exists_affine hx₀
  choose t ht using fun j => QCoh.surjective_app_of_epi S.g hU (c j)
  have hex := (QCoh.exact_iff_stalkLinear S).1 hS.exact x
  obtain ⟨β⟩ := nonempty_basis_of_exact (QCoh.stalkLinear_injective S.f x) hex
    (QCoh.stalkLinear_surjective S.g x) (hb₀.stalkBasis x hx₀) (hc.stalkBasis x hx)
  obtain ⟨V, hV, hxV, e, he⟩ := exists_germ_eq_family hx β
  have hb := (hb₀.res (hV.trans hle)).comp_equiv finSumFinEquiv
  obtain ⟨W, hW, hxW, hv⟩ := exists_isFrame_of_bijective_stalk hb
    (Sum.elim (fun i => S.f.app V (e i)) fun j => resM S.X₂ hV (t j)) hxV (by
      have := (bijective_sumElim_iff (QCoh.stalkLinear_injective S.f x) hex β
        (fun j => S.X₂.presheaf.germ U x hx (t j)) (by
          simp only [QCoh.stalkLinear_germ, ht]
          exact hc.bijective_stalk x hx)).2 (by
          rw [Function.Bijective, ← linearIndependent_iff_injective_fintypeLinearCombination,
            ← LinearMap.range_eq_top, Fintype.range_linearCombination]
          exact ⟨β.linearIndependent, β.span_eq⟩)
      convert this using 3
      funext k
      rcases k with i | j
      · rw [Sum.elim_inl, Sum.elim_inl, ← he, QCoh.stalkLinear_germ]
      · rw [Sum.elim_inr, Sum.elim_inr, germ_resM])
  refine ⟨W, fun i => resM S.X₁ hW (e i), hxW, fun T hT => ?_⟩
  refine (bijective_sumElim_iff (f := appLinear S.f T) (g := appLinear S.g T)
    (QCoh.injective_app_of_mono S.f T) (QCoh.exact_app_of_exact_of_mono hS.exact T) _
    (fun j => resM S.X₂ ((hT.trans hW).trans hV) (t j)) ?_).1 ?_
  · simp only [appLinear_apply, app_resM, ht]
    exact hc T _
  · convert hv T hT using 3
    funext k
    rcases k with i | j
    · simp only [Sum.elim_inl, appLinear_apply, app_resM]
    · simp only [Sum.elim_inr, resM_resM]

end GlobalTheory.VB
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFrameOfBijectiveStalk =====

-- ===== clump member: Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoGenResMapSmulHom =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoGenResMapSmulHom", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsEffAddNsmulDiv\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.ToBidualNaturalityDualSheafTranspose\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasicoherentEigenQuot\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFrameOfBijectiveStalk\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVBAndClsDetOfShortExact\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace TensorProduct IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.QCoh GlobalTheory.CechPic
open GlobalTheory.LB (resG_resG resG_self val_res toMod coord ofSec)
open GlobalTheory.Cartier (IsRegularFn IsRegularSec SecMaps germ_resG ext_germK)
open GlobalTheory.VB (IsVB IsFrame IsSubbundle Chart det)
open GlobalTheory.Twist (resM resM_resM resM_smul app_resM)

namespace GlobalTheory.Vert

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

namespace Model

namespace Hom

variable {Z Z₁ : Model O} (f : Hom Z₁ Z)

instance isProper : IsProper f.f := isProper_of_comp_str f.comp_str

def relDim (_ : Hom Z₁ Z) : ℕ := Z₁.relDim - Z.relDim

abbrev fnField (_ : Hom Z₁ Z) : Type := Z.X.residueField (genericPoint Z.X)

def genFibre : Scheme.{0} := f.f.fiber (genericPoint Z.X)

instance : Nonempty f.genFibre :=
  have ⟨x, hx⟩ := f.f.surjective (genericPoint Z.X)
  ((f.f.range_fiberι _).ge hx).elim fun w _ => ⟨w⟩


end Hom

variable (Z : Model O)

abbrev genRes : Z.X.Modules ⥤ Z.gen.toScheme.Modules := Scheme.Modules.pullback Z.gen.ι

abbrev GenIso (E E' : Z.X.Modules) : Type := Z.genRes.obj E ≅ Z.genRes.obj E'

variable {Z} {Z₁ : Model O} {E E' E'' : Z.X.Modules} {r : ℕ}

def genEquiv {V : Z.X.Opens} (h : V ≤ Z.gen) : Γ(Z.X, V) ≃+* Γ(Z.gen.toScheme, Z.gen.ι ⁻¹ᵁ V) :=
  haveI := Z.gen.ι.isIso_app V (h.trans Z.gen.opensRange_ι.ge)
  (asIso (Z.gen.ι.app V)).commRingCatIsoToRingEquiv

theorem genEquiv_apply {V : Z.X.Opens} (h : V ≤ Z.gen) (a : Γ(Z.X, V)) :
    genEquiv h a = (Z.gen.ι.app V).hom a := rfl

theorem isIso_genRes_map_smulHom (E : Z.X.Modules) {g : O} (hg : g ≠ 0) :
    IsIso (Z.genRes.map (smulHom E (Z.const g))) := by
  rw [VB.pullback_map_smulHom]
  have h : IsUnit (Z.gen.ι.appTop (Z.const g)) :=
    RingedSpace.isUnit_of_isUnit_germ _ _ _ fun x _ => (Scheme.mem_basicOpen_top _ _ x).1
      ((Scheme.preimage_basicOpen_top Z.gen.ι _).le (Z.gen_le_basicOpen hg x.2))
  exact (isUnit_iff_isIso _).1 (h.map (smulEnd _))

namespace GenIso

def ofHom (ψ : E' ⟶ E) [IsIso (Z.genRes.map ψ)] : Z.GenIso E E' := (asIso (Z.genRes.map ψ)).symm


variable (E) in
def smul (g : O) (hg : g ≠ 0) : Z.GenIso E E :=
  haveI := isIso_genRes_map_smulHom E hg
  ofHom (smulHom E (Z.const g))

section Pull

variable {f : Z₁.X ⟶ Z.X} (hf : f ≫ Z.str = Z₁.str)

def genMap : Z₁.gen.toScheme ⟶ Z.gen.toScheme := f.resLE _ _ (preimage_gen hf).ge

def genPullIso : Scheme.Modules.pullback f ⋙ Z₁.genRes ≅
    Z.genRes ⋙ Scheme.Modules.pullback (genMap hf) :=
  Scheme.Modules.pullbackComp _ f ≪≫
    Scheme.Modules.pullbackCongr (f.resLE_comp_ι (preimage_gen hf).ge).symm ≪≫
      (Scheme.Modules.pullbackComp _ _).symm

def pull (φ : Z.GenIso E E') :
    Z₁.GenIso ((Scheme.Modules.pullback f).obj E) ((Scheme.Modules.pullback f).obj E') :=
  (genPullIso hf).app E ≪≫ (Scheme.Modules.pullback (genMap hf)).mapIso φ ≪≫
    ((genPullIso hf).app E').symm

theorem pull_inv {φ : Z.GenIso E E'} {ψ : E' ⟶ E} (h : φ.inv = Z.genRes.map ψ) :
    (φ.pull hf).inv = Z₁.genRes.map ((Scheme.Modules.pullback f).map ψ) := by
  simp only [pull, Iso.trans_inv, Iso.symm_inv, Iso.app_hom, Iso.app_inv, Functor.mapIso_inv, h,
    Category.assoc]
  exact NatIso.naturality_2 (genPullIso hf) ψ

end Pull

variable (φ : Z.GenIso E E')

def detUnit (c : Chart E r) (c' : Chart E' r) [E.IsQuasicoherent] [E'.IsQuasicoherent]
    {T : Z.gen.toScheme.Opens} (h : T ≤ Z.gen.ι ⁻¹ᵁ (c.U ⊓ c'.U)) : Γ(Z.gen.toScheme, T)ˣ :=
  (c.isFrame.pullback Z.gen.ι).detUnit ((c'.isFrame.pullback Z.gen.ι).map_iso φ.inv)
    (h.trans (Z.gen.ι.preimage_mono inf_le_left)) (h.trans (Z.gen.ι.preimage_mono inf_le_right))

theorem detUnit_rel (c d : Chart E r) (c' d' : Chart E' r) [E.IsQuasicoherent]
    [E'.IsQuasicoherent] {V : Z.X.Opens} (hc : V ≤ c.U ⊓ c'.U) (hd : V ≤ d.U ⊓ d'.U)
    {T : Z.gen.toScheme.Opens} (h : T ≤ Z.gen.ι ⁻¹ᵁ V) :
    φ.detUnit c c' (h.trans (Z.gen.ι.preimage_mono hc)) =
      Units.map (Z.gen.ι.appLE V T h).hom.toMonoidHom
        (c.isFrame.detUnit d.isFrame (hc.trans inf_le_left) (hd.trans inf_le_left) *
          (c'.isFrame.detUnit d'.isFrame (hc.trans inf_le_right) (hd.trans inf_le_right))⁻¹) *
        φ.detUnit d d' (h.trans (Z.gen.ι.preimage_mono hd)) := by
  have e := c.isFrame.val_detUnit_pullback d.isFrame Z.gen.ι (hc.trans inf_le_left)
    (hd.trans inf_le_left) h
  have e' := c'.isFrame.val_detUnit_pullback d'.isFrame Z.gen.ι (hc.trans inf_le_right)
    (hd.trans inf_le_right) h
  rw [← (c'.isFrame.pullback Z.gen.ι).detUnit_map_iso _ φ.inv] at e'
  rw [map_mul, map_inv, ← Units.ext (v := Units.map _ _) e, ← Units.ext (v := Units.map _ _) e',
    mul_right_comm, detUnit, detUnit, IsFrame.detUnit_mul, eq_mul_inv_iff_mul_eq,
    IsFrame.detUnit_mul]

def div (hE : IsVB E r) (hE' : IsVB E' r) : VertDiv Z :=
  haveI := hE.isQuasicoherent
  haveI := hE'.isQuasicoherent
  .ofUnits (LB.div (det E r) (det E' r)) (Semi.LB.isLB_div hE.isLB_det hE'.isLB_det)
    (fun p => (genEquiv inf_le_left).symm
      (φ.detUnit p.1 p.2 (Z.gen.ι.preimage_mono inf_le_right)).val)
    (fun _ => (Units.isUnit _).map _) fun p q => by
      have hV := (inf_le_left.trans inf_le_left : Z.gen ⊓ (LB.div (det E r) (det E' r)).U p ⊓
        (LB.div (det E r) (det E' r)).U q ≤ Z.gen)
      have H (p : (LB.div (det E r) (det E' r)).ι) (h) : genEquiv hV (resG Z.X h
          ((genEquiv inf_le_left).symm
            (φ.detUnit p.1 p.2 (Z.gen.ι.preimage_mono inf_le_right)).val)) =
          (φ.detUnit p.1 p.2 (Z.gen.ι.preimage_mono (h.trans inf_le_right))).val := by
        rw [genEquiv_apply, Cartier.app_resG, ← genEquiv_apply inf_le_left,
          RingEquiv.apply_symm_apply]
        exact congrArg Units.val (IsFrame.res_detUnit _ _ _ _ _)
      refine (genEquiv hV).injective ?_
      refine (H p _).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg _ (H q _))).symm)
      rw [φ.detUnit_rel p.1 q.1 p.2 q.2 (inf_le_left.trans inf_le_right)
        inf_le_right le_rfl, Units.val_mul]
      refine congrArg (· * _) ?_
      rw [genEquiv_apply, Scheme.Hom.app_eq_appLE, ← val_res]
      refine congrArg (fun u => (Z.gen.ι.appLE _ _ le_rfl).hom (Units.val u)) ?_
      change _ = res _ (res _ (IsFrame.detUnit _ _ _ _) * (res _ (IsFrame.detUnit _ _ _ _))⁻¹)
      simp only [map_mul, map_inv, IsFrame.res_detUnit]

variable (hE : IsVB E r) (hE' : IsVB E' r) (hE'' : IsVB E'' r)

variable {φ} {ψ : E' ⟶ E}

end GenIso

end Model

structure Flag {X : Scheme.{0}} (E : X.Modules) (N : ℕ) where

  F : Fin (N + 1) → X.Modules

  ι : ∀ i, F i ⟶ E

  isSubbundle : ∀ i, IsSubbundle (ι i)

  isVB : ∀ i, IsVB (F i) i

  step : ∀ i : Fin N, F i.castSucc ⟶ F i.succ

  step_ι : ∀ i, step i ≫ ι i.succ = ι i.castSucc

  isIso_last : IsIso (ι (Fin.last N))

namespace Flag

variable {X : Scheme.{0}} {E : X.Modules} {N : ℕ} (fl : Flag E N)

attribute [instance] isIso_last

attribute [reassoc (attr := simp)] step_ι

instance mono_ι (i : Fin (N + 1)) : Mono (fl.ι i) := (fl.isSubbundle i).mono

instance mono_step (i : Fin N) : Mono (fl.step i) := mono_of_mono_fac (fl.step_ι i)


include fl in
theorem isVB_self : IsVB E N := (fl.isVB (Fin.last N)).of_iso (asIso (fl.ι _))

def gr (i : Fin N) : X.Modules := cokernel (fl.step i)

def π (i : Fin N) : fl.F i.succ ⟶ fl.gr i := cokernel.π _

instance epi_π (i : Fin N) : Epi (fl.π i) := inferInstanceAs (Epi (cokernel.π _))

theorem isVB_cokernel (i : Fin (N + 1)) : IsVB (cokernel (fl.ι i)) (N - i) := fun x => by
  have : Nonempty X := ⟨x⟩
  obtain ⟨s, hs⟩ := (fl.isSubbundle i).isVB_cokernel
  obtain ⟨h, -⟩ := VBExt.isVB_and_cls_det_of_shortExact X (.mk (fl.ι i) (cokernel.π _)
    (cokernel.condition _)) i s { exact := ShortComplex.exact_cokernel _ } (fl.isVB i) hs
  obtain rfl : s = N - i := by have := h.rank_unique fl.isVB_self; omega
  exact hs x

theorem isVB_gr (i : Fin N) : IsVB (fl.gr i) 1 := by
  refine VB.isVB_X₁_of_shortExact X _ 1 _ (shortExact_cokernel_comp (fl.step i) (fl.ι i.succ)) ?_
    (fl.isVB_cokernel i.succ)
  have h := (fl.isVB_cokernel i.castSucc).of_iso (cokernelIsoOfEq (fl.step_ι i).symm)
  rwa [show N - (i.castSucc : ℕ) = 1 + (N - (i.succ : ℕ)) by simp; omega] at h

def root (i : Fin N) : LB X := det (fl.gr i) 1

def ofIso {E' : X.Modules} (e : E ≅ E') : Flag E' N where
  F := fl.F
  ι i := fl.ι i ≫ e.hom
  isSubbundle i := ⟨inferInstance, _, (fl.isVB_cokernel i).of_iso (cokernelCompIsIso _ _).symm⟩
  isVB := fl.isVB
  step := fl.step
  step_ι i := fl.step_ι_assoc i _
  isIso_last := inferInstance



end Flag

namespace Model

variable {Z : Model O} {E E' : Z.X.Modules} {N : ℕ}

structure FlagPair (φ : Z.GenIso E E') (N : ℕ) where

  fl : Flag E N

  fl' : Flag E' N

  gen : ∀ i, Z.GenIso (fl.F i) (fl'.F i)

  gen_ι : ∀ i, (gen i).hom ≫ Z.genRes.map (fl'.ι i) = Z.genRes.map (fl.ι i) ≫ φ.hom

instance mono_genRes_map_ι (fl : Flag E N) (i : Fin (N + 1)) : Mono (Z.genRes.map (fl.ι i)) :=
  have := (fl.isVB i).isQuasicoherent
  have := fl.isVB_self.isQuasicoherent
  mono_pullback_map _ _

namespace FlagPair

variable {φ : Z.GenIso E E'} (P : FlagPair φ N)

theorem gen_step (i : Fin N) : Z.genRes.map (P.fl.step i) ≫ (P.gen i.succ).hom =
    (P.gen i.castSucc).hom ≫ Z.genRes.map (P.fl'.step i) := by
  rw [← cancel_mono (Z.genRes.map (P.fl'.ι i.succ)), Category.assoc, Category.assoc, gen_ι,
    ← Functor.map_comp, ← Functor.map_comp_assoc, Flag.step_ι, Flag.step_ι, gen_ι]

def grIso (i : Fin N) : Z.GenIso (P.fl.gr i) (P.fl'.gr i) :=
  PreservesCokernel.iso Z.genRes (P.fl.step i) ≪≫
    cokernel.mapIso _ _ (P.gen i.castSucc) (P.gen i.succ) (P.gen_step i) ≪≫
      (PreservesCokernel.iso Z.genRes (P.fl'.step i)).symm

def div (i : Fin N) : VertDiv Z := (P.grIso i).div (P.fl.isVB_gr i) (P.fl'.isVB_gr i)

end FlagPair

structure FlagModel (φ : Z.GenIso E E') (N : ℕ) where

  B : Model O

  π : Hom B Z

  pair : FlagPair (φ.pull π.comp_str) N

def FlagModel.relDim {φ : Z.GenIso E E'} (M : FlagModel φ N) : ℕ := M.π.relDim

end Model

end GlobalTheory.Vert
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoGenResMapSmulHom =====
