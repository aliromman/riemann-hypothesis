module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.PairingExtends
public import Mathlib.GroupTheory.IndexNSmul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.WeilBound.CoreStatements.HodgeTatePoints.TwpdivHopf, Development.WeilBound.CoreStatements.HodgeTatePoints.TwpdivTate, Development.WeilBound.CoreStatements.HodgeTatePoints.Twpdiv

-- ===== clump member: Development.WeilBound.CoreStatements.HodgeTatePoints.TwpdivHopf =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.HodgeTatePoints.TwpdivHopf", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective\npublic import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace PositivityTheory.HtPt.Twpdiv

open TensorProduct GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.PDiv Coalgebra Bialgebra WithConv

section Sep

variable {R : Type} [CommRing R] {M N P M' N' : Type} [CommRing M] [Algebra R M] [CommRing N] [Algebra R N]
  [CommRing P] [Algebra R P] [CommRing M'] [Algebra R M'] [CommRing N'] [Algebra R N']

def pair (x : M →ₐ[R] R) (y : N →ₐ[R] R) : M ⊗[R] N →ₐ[R] R :=
  Algebra.TensorProduct.lift x y (fun _ _ => Commute.all _ _)

theorem pair_map (x : M →ₐ[R] R) (y : N →ₐ[R] R) (f : M' →ₐ[R] M) (g : N' →ₐ[R] N) (z : M' ⊗[R] N') :
    pair x y (Algebra.TensorProduct.map f g z) = pair (x.comp f) (y.comp g) z := by
  induction z <;> simp_all [pair]

theorem pair_assoc (x : M →ₐ[R] R) (y : N →ₐ[R] R) (w : P →ₐ[R] R) (z : (M ⊗[R] N) ⊗[R] P) :
    pair x (pair y w) (Algebra.TensorProduct.assoc R R R M N P z) = pair (pair x y) w z := by
  have : (pair x (pair y w)).comp (Algebra.TensorProduct.assoc R R R M N P).toAlgHom = pair (pair x y) w := by
    ext <;> simp [Algebra.TensorProduct.one_def, pair]
  exact DFunLike.congr_fun this z

theorem pair_comm (x : M →ₐ[R] R) (y : N →ₐ[R] R) (z : N ⊗[R] M) :
    pair x y (TensorProduct.comm R N M z) = pair y x z := by
  induction z <;> simp_all [pair, mul_comm]

theorem comp_lift (x : M →ₐ[R] R) (f : N →ₐ[R] M) (g : P →ₐ[R] M) (h) (z : N ⊗[R] P) :
    x (Algebra.TensorProduct.lift f g h z) = pair (x.comp f) (x.comp g) z := by
  induction z <;> simp_all [pair]

def Sep {S : Type} (ev : S → (M →ₐ[R] R)) : Prop := ∀ a b : M, (∀ s, ev s a = ev s b) → a = b

theorem Sep.pair {S S' : Type} [Finite S'] [Module.Flat R M] {ev : S → (M →ₐ[R] R)} {ev' : S' → (N →ₐ[R] R)}
    (h : Sep ev) (h' : Sep ev') : Sep (fun z : S × S' => pair (ev z.1) (ev' z.2)) := by
  classical
  have := Fintype.ofFinite S'
  intro a b hab
  let i : N →ₗ[R] (S' → R) := LinearMap.pi fun t => (ev' t).toLinearMap
  have hi : Function.Injective i := fun u v huv => h' u v fun t => congrFun huv t
  apply Module.Flat.lTensor_preserves_injective_linearMap (M := M) i hi
  apply (TensorProduct.piScalarRight R R M S').injective
  funext t
  refine h _ _ fun s => ?_
  have key : ∀ z : M ⊗[R] N, ev s (TensorProduct.piScalarRight R R M S' (i.lTensor M z) t) =
      Twpdiv.pair (ev s) (ev' t) z := by
    intro z
    induction z with
    | tmul u v => simp [i, mul_comm, Twpdiv.pair]
    | add u v hu hv => simp only [map_add (f := _), Pi.add_apply, hu, hv]
  rw [key, key]
  exact hab (s, t)

end Sep

variable {R : Type} [CommRing R] {T : Type} [CommGroup T] {A : Subalgebra R (T → R)}

def Ord (_ : IsHopfOrder A) : Type := A

namespace Ord

variable (h : IsHopfOrder A)

instance : CommRing (Ord h) := inferInstanceAs (CommRing A)
instance : Algebra R (Ord h) := inferInstanceAs (Algebra R A)
instance : Module.Finite R (Ord h) := h.finite
instance : Module.Projective R (Ord h) := h.projective

def equiv : Ord h ≃ₐ[R] A := AlgEquiv.refl

def ev (t : T) : Ord h →ₐ[R] R := (evalAt A t).comp (equiv h).toAlgHom

theorem sep : Sep (ev h) := fun _ _ hab => (equiv h).injective (Subtype.ext (funext hab))

def liftTo {B : Type} [CommRing B] [Algebra R B] {S : Type} (e : S → (B →ₐ[R] R)) (he : Sep e)
    {B' : Type} [CommRing B'] [Algebra R B'] (e' : S → (B' →ₐ[R] R)) (H : ∀ f, ∃ g, ∀ s, e s g = e' s f) :
    B' →ₐ[R] B where
  toFun f := (H f).choose
  map_one' := he _ _ fun s => by rw [(H _).choose_spec, map_one, map_one]
  map_mul' a b := he _ _ fun s => by
    rw [map_mul, (H a).choose_spec, (H b).choose_spec, (H _).choose_spec, map_mul]
  map_zero' := he _ _ fun s => by rw [(H _).choose_spec, map_zero, map_zero]
  map_add' a b := he _ _ fun s => by
    rw [map_add (f := _), (H a).choose_spec, (H b).choose_spec, (H _).choose_spec, map_add (f := _)]
  commutes' _ := he _ _ fun s => by rw [(H _).choose_spec, AlgHom.commutes, AlgHom.commutes]

theorem ev_liftTo {B : Type} [CommRing B] [Algebra R B] {S : Type} (e : S → (B →ₐ[R] R)) (he : Sep e)
    {B' : Type} [CommRing B'] [Algebra R B'] (e' : S → (B' →ₐ[R] R)) (H : ∀ f, ∃ g, ∀ s, e s g = e' s f)
    (s : S) : (e s).comp (liftTo e he e' H) = e' s := AlgHom.ext fun f => (H f).choose_spec s

theorem exists_of_mem_prodSpan {g : T × T → R} (hg : g ∈ prodSpan A) :
    ∃ z : Ord h ⊗[R] Ord h, ∀ s : T × T, pair (ev h s.1) (ev h s.2) z = g s := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hg
    exact ⟨(equiv h).symm ⟨a, ha⟩ ⊗ₜ (equiv h).symm ⟨b, hb⟩, fun s => rfl⟩
  | zero => exact ⟨0, fun s => by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨a, ha⟩ := hu
    obtain ⟨b, hb⟩ := hv
    exact ⟨a + b, fun s => by simp [ha, hb]⟩
  | smul c u _ hu =>
    obtain ⟨a, ha⟩ := hu
    exact ⟨c • a, fun s => by simp [ha]⟩

def anti : Ord h →ₐ[R] Ord h :=
  liftTo (ev h) (sep h) (fun t => ev h t⁻¹) fun f => ⟨(equiv h).symm ⟨_, h.inv _ (equiv h f).2⟩, fun _ => rfl⟩

theorem ev_anti (t : T) : (ev h t).comp (anti h) = ev h t⁻¹ := ev_liftTo _ _ _ _ t

variable [Finite T]

theorem sep₂ : Sep (fun z : T × T => pair (ev h z.1) (ev h z.2)) := (sep h).pair (sep h)

def delta : Ord h →ₐ[R] Ord h ⊗[R] Ord h :=
  liftTo _ (sep₂ h) (fun z => ev h (z.1 * z.2)) fun f => exists_of_mem_prodSpan h (h.comul _ (equiv h f).2)

theorem pair_comp_delta (s t : T) : (pair (ev h s) (ev h t)).comp (delta h) = ev h (s * t) :=
  ev_liftTo _ (sep₂ h) _ _ (s, t)

theorem pair_delta (s t : T) (f : Ord h) : pair (ev h s) (ev h t) (delta h f) = ev h (s * t) f :=
  DFunLike.congr_fun (pair_comp_delta h s t) f

theorem sep_id : Sep (fun _ : Unit => AlgHom.id R R) := fun _ _ h => h ()

instance : Bialgebra R (Ord h) :=
  Bialgebra.ofAlgHom (delta h) (ev h 1)
    (AlgHom.ext fun f => (sep h).pair (sep₂ h) _ _ fun z => by
      refine (pair_assoc _ _ _ (Algebra.TensorProduct.map (delta h) (AlgHom.id R _) (delta h f))).trans ?_
      simp only [AlgHom.comp_apply, pair_map, pair_comp_delta, AlgHom.comp_id, pair_delta, mul_assoc])
    (AlgHom.ext fun f => sep_id.pair (sep h) _ _ fun z => by
      simp [pair_map, pair_delta]
      simp [pair])
    (AlgHom.ext fun f => (sep h).pair sep_id _ _ fun z => by
      simp [pair_map, pair_delta]
      simp [pair])

theorem comul_eq (f : Ord h) : comul (R := R) f = delta h f := rfl

theorem counit_eq (f : Ord h) : counit (R := R) f = ev h 1 f := rfl

instance : HopfAlgebra R (Ord h) :=
  HopfAlgebra.ofAlgHom (anti h)
    (AlgHom.ext fun f => sep h _ _ fun t => by
      refine (comp_lift (ev h t) (anti h) (AlgHom.id R _) (fun _ _ => Commute.all _ _) (delta h f)).trans ?_
      simp [ev_anti, counit_eq, pair_delta, Algebra.ofId_apply])
    (AlgHom.ext fun f => sep h _ _ fun t => by
      refine (comp_lift (ev h t) (AlgHom.id R _) (anti h) (fun _ _ => Commute.all _ _) (delta h f)).trans ?_
      simp [ev_anti, counit_eq, pair_delta, Algebra.ofId_apply])

instance : IsCocomm R (Ord h) :=
  ⟨LinearMap.ext fun f => sep₂ h _ _ fun z => by
    simp [pair_comm, comul_eq, pair_delta, mul_comm]⟩

def evHom : T →* WithConv (Ord h →ₐ[R] R) where
  toFun t := toConv (ev h t)
  map_one' := by ext f; simp [counit_eq]
  map_mul' s t := by
    ext f
    rw [AlgHom.convMul_apply]
    exact (pair_delta h s t f).symm

theorem evHom_apply (t : T) : evHom h t = toConv (ev h t) := rfl

theorem ev_mulBy (t : T) (k : ℕ) (f : Ord h) :
    ev h t (mulBy (R := R) (A := Ord h) k f) = ev h (t ^ k) f := by
  have h1 := comp_mulBy_pts (ev h t) k
  rw [← evHom_apply, ← map_pow] at h1
  exact DFunLike.congr_fun h1 f

theorem evHom_bijective [IsDomain R] : Function.Bijective (evHom h) := by
  classical
  have := Fintype.ofFinite T
  obtain ⟨d, hd, hA⟩ := h.full
  let e : T → Ord h := fun t => (equiv h).symm ⟨_, hA (Pi.single t 1)⟩
  have he : ∀ s t, ev h s (e t) = if s = t then d else 0 := fun s t => by
    change d • (Pi.single t (1 : R) : T → R) s = _
    simp [Pi.single_apply]
  constructor
  · intro s t hst
    have h1 : ev h s (e t) = ev h t (e t) := DFunLike.congr_fun (congrArg ofConv hst) (e t)
    rw [he, he, ite_eq_left rfl] at h1
    by_contra hne
    rw [ite_eq_right hne] at h1
    exact hd h1.symm
  · intro x
    have h1 : ∑ t, e t = algebraMap R _ d := sep h _ _ fun s => by simp [he]
    obtain ⟨t, ht⟩ : ∃ t, x.ofConv (e t) ≠ 0 := by
      by_contra! H
      have := congrArg x.ofConv h1
      simp [H] at this
      exact hd this.symm
    refine ⟨t, ofConv_injective (AlgHom.ext fun f => ?_)⟩
    have h2 : f * e t = ev h t f • e t := sep h _ _ fun s => by
      by_cases hs : s = t <;> simp [he, hs]
    have h3 := congrArg x.ofConv h2
    rw [map_mul, map_smul, smul_eq_mul] at h3
    exact (mul_right_cancel₀ ht h3).symm

theorem finrank_eq [IsDomain R] : Module.finrank R (Ord h) = Nat.card T := by
  have := Fintype.ofFinite T
  obtain ⟨d, hd, hA⟩ := h.full
  rw [Nat.card_eq_fintype_card, ← Module.finrank_fintype_fun_eq_card R]
  apply le_antisymm
  · exact LinearMap.finrank_le_finrank_of_injective (f := A.val.toLinearMap ∘ₗ (equiv h).toLinearMap)
      (Subtype.val_injective.comp (equiv h).injective)
  · refine LinearMap.finrank_le_finrank_of_injective (f := (equiv h).symm.toLinearMap ∘ₗ
      LinearMap.codRestrict A.toSubmodule (d • LinearMap.id) hA) ?_
    intro u v huv
    have h1 : d • u = d • v := congrArg Subtype.val ((equiv h).symm.injective huv)
    funext t
    exact mul_left_cancel₀ hd (congrFun h1 t)

theorem rankAtStalk_eq [IsDomain R] [IsLocalRing R] (q : PrimeSpectrum R) :
    Module.rankAtStalk (Ord h) q = Nat.card T := by
  have : Module.Free R (Ord h) := Module.free_of_flat_of_isLocalRing
  rw [Module.rankAtStalk_eq_finrank_of_free, finrank_eq]
  rfl

def comap {T' : Type} [CommGroup T'] [Finite T'] {A' : Subalgebra R (T' → R)} (h' : IsHopfOrder A') (ι : T →* T')
    (H : ∀ f ∈ A', (fun t => f (ι t)) ∈ A) : Ord h' →ₐc[R] Ord h :=
  let φ : Ord h' →ₐ[R] Ord h := liftTo (ev h) (sep h) (fun t => ev h' (ι t)) fun f =>
    ⟨(equiv h).symm ⟨_, H _ (equiv h' f).2⟩, fun _ => rfl⟩
  have hφ : ∀ t, (ev h t).comp φ = ev h' (ι t) := ev_liftTo _ _ _ _
  have hφ' : ∀ t f, ev h t (φ f) = ev h' (ι t) f := fun t f => DFunLike.congr_fun (hφ t) f
  BialgHom.ofAlgHom φ (AlgHom.ext fun f => by simp [counit_eq, hφ'])
    (AlgHom.ext fun f => sep₂ h _ _ fun z => by simp [pair_map, comul_eq, hφ, hφ', pair_delta])

theorem ev_comap {T' : Type} [CommGroup T'] [Finite T'] {A' : Subalgebra R (T' → R)} (h' : IsHopfOrder A')
    (ι : T →* T') (H : ∀ f ∈ A', (fun t => f (ι t)) ∈ A) (t : T) (f : Ord h') :
    ev h t (comap h h' ι H f) = ev h' (ι t) f :=
  DFunLike.congr_fun (ev_liftTo (ev h) (sep h) (fun t => ev h' (ι t)) (fun f =>
    ⟨(equiv h).symm ⟨_, H _ (equiv h' f).2⟩, fun _ => rfl⟩) t) f

end Ord

end PositivityTheory.HtPt.Twpdiv
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.HodgeTatePoints.TwpdivHopf =====

-- ===== clump member: Development.WeilBound.CoreStatements.HodgeTatePoints.TwpdivTate =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.HodgeTatePoints.TwpdivTate", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace PositivityTheory.HtPt.Twpdiv

open TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup WithConv

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {G : PDivGroup p O}

def lvl (G : PDivGroup p O) (n : ℕ) : G.Tate →+ Additive (WithConv (G.A n →ₐ[O] O)) where
  toFun x := Additive.ofMul (x.conv n)
  map_zero' := rfl
  map_add' _ _ := rfl

theorem lvl_smul (n : ℕ) (a : ℤ_[p]) (x : G.Tate) : lvl G n (a • x) = digit n a • lvl G n x := rfl

theorem tate_equiv {La : Type} [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (τ : La →+ G.Tate)
    (h1 : ∀ n a a', (τ a).conv n = (τ a').conv n ↔ ∃ b : La, a - a' = (p ^ n) • b)
    (h2 : ∀ n y, ∃ a, (τ a).conv n = y) :
    ∃ j : ℤ_[p] ⊗[ℤ] La ≃ₗ[ℤ_[p]] G.Tate, ∀ a, j (1 ⊗ₜ a) = τ a := by
  classical
  let j : ℤ_[p] ⊗[ℤ] La →ₗ[ℤ_[p]] G.Tate := LinearMap.liftBaseChange ℤ_[p] τ.toIntLinearMap
  have hj : ∀ (c : ℤ_[p]) a, j (c ⊗ₜ a) = c • τ a := fun c a => rfl
  let b := Module.Free.chooseBasis ℤ La
  have key : ∀ (c : Module.Free.ChooseBasisIndex ℤ La → ℤ_[p]) n,
      (j (∑ i, c i ⊗ₜ b i)).conv n = (τ (∑ i, digit n (c i) • b i)).conv n := by
    intro c n
    change lvl G n _ = lvl G n _

    simp only [map_sum, hj, lvl_smul, map_nsmul]
  have hdiv : ∀ n (a a' : La), (∃ u : La, a - a' = (p ^ n) • u) ↔
      ∀ i, ((b.repr a i : ℤ) : ZMod (p ^ n)) = (b.repr a' i : ℤ) := by
    intro n a a'
    simp only [ZMod.intCast_eq_intCast_iff_dvd_sub]
    constructor
    · rintro ⟨u, hu⟩ i
      have := congrArg (fun x => b.repr x i) hu
      simp only [map_sub, map_nsmul, Finsupp.sub_apply, Finsupp.smul_apply, nsmul_eq_mul] at this
      rw [dvd_sub_comm]
      exact ⟨_, this⟩
    · intro H
      choose u hu using fun i => dvd_sub_comm.1 (H i)
      refine ⟨b.equivFun.symm u, b.equivFun.injective (funext fun i => ?_)⟩
      rw [map_nsmul, LinearEquiv.apply_symm_apply, map_sub]
      simpa using hu i
  have hrep : ∀ (k : Module.Free.ChooseBasisIndex ℤ La → ℕ) i, b.repr (∑ i, k i • b i) i = k i := by
    intro k i
    have : ∑ i, k i • b i = b.equivFun.symm fun i => (k i : ℤ) := by simp
    rw [this, ← b.equivFun_apply, LinearEquiv.apply_symm_apply]
  refine ⟨LinearEquiv.ofBijective j ⟨?_, fun x => ?_⟩, fun a => (hj 1 a).trans (one_smul _ _)⟩
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨c, rfl⟩ : ∃ c : Module.Free.ChooseBasisIndex ℤ La → ℤ_[p], z = ∑ i, c i ⊗ₜ b i := by
      refine ⟨(b.baseChange ℤ_[p]).repr z, ?_⟩
      conv_lhs => rw [← (b.baseChange ℤ_[p]).sum_repr z]
      simp [TensorProduct.smul_tmul']
    have hc : ∀ i, c i = 0 := fun i => PadicInt.ext_of_toZModPow.1 fun n => by
      have h3 := key c n
      rw [hz, ← map_zero τ] at h3
      have h4 := (hdiv n _ _).1 ((h1 n _ _).1 h3) i
      rw [hrep] at h4
      rw [map_zero, ← cast_digit]
      simpa using h4.symm
    simp [hc]
  · choose a ha using fun n => h2 n (x.conv n)
    have hc : ∀ n, (τ (a (n + 1))).conv n = (τ (a n)).conv n := fun n => by
      rw [← TateOver.compat_conv, ha, ha, TateOver.compat_conv]
    have hd : ∀ i n, (p : ℤ) ^ n ∣ b.repr (a (n + 1)) i - b.repr (a n) i := fun i n => by
      have := (hdiv n _ _).1 ((h1 n _ _).1 (hc n).symm) i
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at this
      exact_mod_cast this
    refine ⟨∑ i, PadicInt.ofIntSeq _ (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub
      (fun n => b.repr (a n) i) p (hd i)) ⊗ₜ b i,
      TateOver.ext_conv fun n => ?_⟩
    rw [key, ← ha, h1, hdiv]
    intro i
    rw [hrep, Int.cast_natCast, cast_digit, PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub
      (fun n => b.repr (a n) i) p (hd i)]

end PositivityTheory.HtPt.Twpdiv
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.HodgeTatePoints.TwpdivTate =====

-- ===== clump member: Development.WeilBound.CoreStatements.HodgeTatePoints.Twpdiv =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.HodgeTatePoints.Twpdiv", "h": "module\n\npublic import Development.WeilBound.CoreStatements.HodgeTatePoints.TwpdivHopf\npublic import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.PairingExtends\npublic import Development.WeilBound.CoreStatements.HodgeTatePoints.TwpdivTate\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\npublic import Mathlib.GroupTheory.IndexNSmul\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace PositivityTheory.HtPt.Twpdiv

open TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup WithConv GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT Coalgebra Bialgebra

section Lev

variable {La : Type} [AddCommGroup La] (p : ℕ)

theorem lev_surjective (n : ℕ) : Function.Surjective (lev (La := La) p n) := fun t =>
  Submodule.Quotient.mk_surjective _ (Multiplicative.toAdd t)

theorem lev_eq_iff (n : ℕ) (a a' : La) : lev p n a = lev p n a' ↔ ∃ b : La, a - a' = (p ^ n) • b := by
  rw [lev, lev, Multiplicative.ofAdd.apply_eq_iff_eq, Submodule.Quotient.eq]
  exact ⟨fun ⟨b, hb⟩ => ⟨b, hb.symm⟩, fun ⟨b, hb⟩ => ⟨b, hb.symm⟩⟩

theorem lev_add (n : ℕ) (a a' : La) : lev p n (a + a') = lev p n a * lev p n a' := rfl

theorem lev_zero (n : ℕ) : lev p n (0 : La) = 1 := rfl

theorem lev_nsmul (n k : ℕ) (a : La) : lev p n (k • a) = lev p n a ^ k := by
  induction k with
  | zero => simp [lev_zero]
  | succ k ih => rw [succ_nsmul, lev_add, ih, pow_succ]

theorem lev_pow (n : ℕ) (t : LevGrp La p n) : t ^ p ^ n = 1 := by
  obtain ⟨a, rfl⟩ := lev_surjective p n t
  rw [← lev_nsmul, ← lev_zero, lev_eq_iff]
  exact ⟨a, sub_zero _⟩

def incl (n : ℕ) : LevGrp La p n →* LevGrp La p (n + 1) :=
  AddMonoidHom.toMultiplicative (Submodule.mapQ _ _ (p • (LinearMap.id : La →ₗ[ℤ] La)) (by
    rintro _ ⟨b, rfl⟩
    exact ⟨b, by simp only [LinearMap.smul_apply, LinearMap.id_apply, pow_succ', mul_smul]⟩)).toAddMonoidHom

theorem incl_lev (n : ℕ) (a : La) : incl p n (lev p n a) = lev p (n + 1) (p • a) := rfl

theorem card_lev [Module.Free ℤ La] [Module.Finite ℤ La] (n : ℕ) :
    Nat.card (LevGrp La p n) = p ^ (n * Module.finrank ℤ La) := by
  rw [pow_mul, ← AddSubgroup.index_range_nsmul]
  have : (nsmulAddMonoidHom (α := La) (p ^ n)).range =
      (LinearMap.range ((p ^ n) • (LinearMap.id : La →ₗ[ℤ] La))).toAddSubgroup := by
    ext x; exact Iff.rfl
  rw [this]
  rfl

instance [Fact p.Prime] [Module.Free ℤ La] [Module.Finite ℤ La] (n : ℕ) : Finite (LevGrp La p n) :=
  Nat.finite_of_card_ne_zero (by rw [card_lev]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)

end Lev

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {La : Type} [AddCommGroup La] [Module.Free ℤ La]
  [Module.Finite ℤ La] {L : Type} [AddCommGroup L] [Module O L] (X : OrdTower p O La L)

def resT (n : ℕ) : Ord (X.hopf (n + 1)) →ₐc[O] Ord (X.hopf n) :=
  Ord.comap (X.hopf n) (X.hopf (n + 1)) (incl p n) fun f hf => (X.res_iff n _).2 ⟨f, hf, fun _ => rfl⟩

theorem ev_resT (n : ℕ) (t : LevGrp La p n) (f : Ord (X.hopf (n + 1))) :
    Ord.ev _ t (resT X n f) = Ord.ev _ (incl p n t) f := Ord.ev_comap _ _ _ _ t f

theorem resT_surjective (n : ℕ) : Function.Surjective (resT X n) := fun g => by
  obtain ⟨f, hf, h⟩ := (X.res_iff n _).1 (Ord.equiv _ g).2
  refine ⟨(Ord.equiv _).symm ⟨f, hf⟩, Ord.sep _ _ _ fun t => ?_⟩
  obtain ⟨a, rfl⟩ := lev_surjective p n t
  rw [ev_resT]
  exact (h a).symm

theorem ker_resT (n : ℕ) :
    RingHom.ker (resT X n) = torsionIdeal (R := O) (A := Ord (X.hopf (n + 1))) (p ^ n) := by
  apply le_antisymm
  · intro f hf
    have hf' : resT X n f = 0 := hf
    have h1 := X.ker_res n (Ord.equiv _ f) fun a => by
      have := ev_resT X n (lev p n a) f
      rw [hf', map_zero] at this
      exact this.symm
    have h2 : Ideal.span {g : X.A (n + 1) | ∃ h ∈ X.A (n + 1), ∀ t, g.1 t = h (t ^ p ^ n) - h 1} ≤
        (torsionIdeal (R := O) (A := Ord (X.hopf (n + 1))) (p ^ n)).comap
          (Ord.equiv (X.hopf (n + 1))).symm := by
      rw [Ideal.span_le]
      rintro g ⟨u, hu, hg⟩
      let u' := (Ord.equiv (X.hopf (n + 1))).symm ⟨u, hu⟩
      have h3 : (Ord.equiv (X.hopf (n + 1))).symm g =
          mulBy (R := O) (A := Ord (X.hopf (n + 1))) (p ^ n)
            (u' - algebraMap O _ (counit u')) := Ord.sep _ _ _ fun t => by
        rw [Ord.ev_mulBy, map_sub, AlgHom.commutes, Ord.counit_eq]
        exact hg t
      change (Ord.equiv (X.hopf (n + 1))).symm g ∈ torsionIdeal (R := O) (A := Ord (X.hopf (n + 1))) (p ^ n)
      rw [h3]
      have hu' : u' - algebraMap O _ (counit u') ∈ augIdeal (R := O) (A := Ord (X.hopf (n + 1))) := by
        change counit (R := O) (u' - algebraMap O _ (counit (R := O) u')) = 0
        rw [map_sub, counit_algebraMap, sub_self]
      unfold torsionIdeal kerIdeal
      exact Ideal.mem_map_of_mem (mulBy (R := O) (A := Ord (X.hopf (n + 1))) (p ^ n)).toAlgHom hu'
    exact h2 h1
  · refine (kerIdeal_le_ker_iff _ (resT X n : Ord (X.hopf (n + 1)) →ₐ[O] Ord (X.hopf n))).2 fun c =>
      Ord.sep _ _ _ fun t => ?_
    rw [AlgHom.commutes]
    change Ord.ev _ t (resT X n _) = _
    rw [ev_resT, Ord.ev_mulBy, ← map_pow, lev_pow, map_one, Ord.counit_eq]
    rfl

variable [IsDomain O] [IsLocalRing O]

def grp : PDivGroup p O where
  height := Module.finrank ℤ La
  A n := Ord (X.hopf n)
  rank_eq n q := by rw [Ord.rankAtStalk_eq, card_lev]
  res := resT X
  res_surjective := resT_surjective X
  ker_res := ker_resT X

def tau : La →+ (grp X).Tate :=
  AddMonoidHom.mk' (fun a => ⟨fun n => Ord.ev (X.hopf n) (lev p n a), fun n => AlgHom.ext fun g => by
      obtain ⟨f, rfl⟩ := (grp X).res_surjective n g
      refine (congrArg (Ord.ev (X.hopf (n + 1)) (lev p (n + 1) a)) ((grp X).mulP_res n f)).trans ?_
      refine (Ord.ev_mulBy _ _ p f).trans ?_
      rw [← lev_nsmul]
      exact (ev_resT X n (lev p n a) f).symm⟩)
    fun a b => TateOver.ext_conv fun n => map_mul (Ord.evHom (X.hopf n)) (lev p n a) (lev p n b)

theorem realises : X.Realises (grp X) (fun n => Ord.equiv (X.hopf n)) (tau X) :=
  ⟨fun n f a => ev_resT X n (lev p n a) f, fun _ _ _ => rfl⟩

theorem exists_tate : ∃ j : ℤ_[p] ⊗[ℤ] La ≃ₗ[ℤ_[p]] (grp X).Tate, ∀ a, j (1 ⊗ₜ a) = tau X a :=
  tate_equiv (tau X)
    (fun n a a' => ((Ord.evHom_bijective (X.hopf n)).1.eq_iff (a := lev p n a) (b := lev p n a')).trans
      (lev_eq_iff p n a a'))
    fun n y => by
      obtain ⟨t, ht⟩ := (Ord.evHom_bijective (X.hopf n)).2 y
      obtain ⟨a, rfl⟩ := lev_surjective p n t
      exact ⟨a, ht⟩

end PositivityTheory.HtPt.Twpdiv

end

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

theorem PositivityTheory.HtPt.Twpdiv.tower_pdiv : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (L : Type) [AddCommGroup L] [Module O L] (X : OrdTower p O La L), ∃ (G : PDivGroup p O) (e : ∀ n, G.A n ≃ₐ[O] X.A n) (τ : La →+ G.Tate), X.Realises G e τ ∧ G.height = Module.finrank ℤ La ∧ ∃ j : ℤ_[p] ⊗[ℤ] La ≃ₗ[ℤ_[p]] G.Tate, ∀ a, j (1 ⊗ₜ a) = τ a := by
  intro p _ C _ _ _ v O _ _ _ hv _ _ La _ _ _ L _ _ X
  have : ValuationRing O := ValuationRing.of_integers v hv
  exact ⟨PositivityTheory.HtPt.Twpdiv.grp X, _, _, PositivityTheory.HtPt.Twpdiv.realises X, rfl, PositivityTheory.HtPt.Twpdiv.exists_tate X⟩
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.HodgeTatePoints.Twpdiv =====
