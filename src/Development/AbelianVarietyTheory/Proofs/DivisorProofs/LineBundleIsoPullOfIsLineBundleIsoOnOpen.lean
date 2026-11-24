module

public import Development.AbelianVarietyTheory.Definitions.Divisors.WhiskerLeftEqLift
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleGlueOfOpenCoverCocycle, Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoPullOfIsLineBundleIsoOnOpen

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleGlueOfOpenCoverCocycle =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleGlueOfOpenCoverCocycle", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.WhiskerLeftEqLift\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PicGlue

variable {X : Scheme.{0}} {Ix : Type}

def sigmaGlue (W : Ix → X.Opens) (L : Ix → LB X) (w : ∀ i k, Cmp (W i ⊓ W k) (L i) (L k))
    (hL : ∀ i, IsOn (W i) (L i)) : LB X :=
  ⟨Σ i, (L i).ι, fun p ↦ (L p.1).U p.2,
    fun p q ↦ res (le_inf (inf_le_inf ((hL p.1).le p.2) ((hL q.1).le q.2)) le_rfl) (w p.1 q.1 p.2 q.2)⟩

theorem gm_sigmaGlue_g (W : Ix → X.Opens) (L : Ix → LB X) (w : ∀ i k, Cmp (W i ⊓ W k) (L i) (L k))
    (hL : ∀ i, IsOn (W i) (L i)) (x : X) (p q : (sigmaGlue W L w hL).ι)
    (hp : x ∈ (L p.1).U p.2) (hq : x ∈ (L q.1).U q.2) :
    gm (𝟙 X) x _ ((sigmaGlue W L w hL).g p q) = gm (𝟙 X) x _ (w p.1 q.1 p.2 q.2) :=
  gm_res (𝟙 X) x _ (show x ∈ (L p.1).U p.2 ⊓ (L q.1).U q.2 from ⟨hp, hq⟩) _

theorem lb_glue : ∀ (X : Scheme.{0}) (Ix : Type) (W : Ix → X.Opens) (L : Ix → LB X) (w : ∀ i k, Cmp (W i ⊓ W k) (L i) (L k)), (∀ x, ∃ i, x ∈ W i) → (∀ i, IsOn (W i) (L i)) → (∀ i k, IsoOn (W i ⊓ W k) (L i) (L k) (w i k)) → (∀ (i j k : Ix) (x : X) (a : (L i).ι) (b : (L j).ι) (c : (L k).ι), x ∈ (L i).U a → x ∈ (L j).U b → x ∈ (L k).U c → gm (𝟙 X) x _ (w i j a b) * gm (𝟙 X) x _ (w j k b c) = gm (𝟙 X) x _ (w i k a c)) → ∃ N : LB X, N.IsLB ∧ ∀ i, ∃ v : Cmp (W i) N (L i), IsoOn (W i) N (L i) v := by
  intro X Ix W L w hW hL hiso hcoc
  have hdiag : ∀ i (a : (L i).ι) (x : X), x ∈ (L i).U a → gm (𝟙 X) x _ (w i i a a) = 1 :=
    fun i a x ha ↦ mul_eq_left.1 (hcoc i i i x a a a ha ha ha)
  have hgi : ∀ i (x : X) (b b' : (L i).ι), x ∈ (L i).U b → x ∈ (L i).U b' → x ∈ W i →
      gm (𝟙 X) x _ ((L i).g b b') = gm (𝟙 X) x _ (w i i b b') := by
    intro i x b b' hb hb' hx
    have h1 := hiso i i x ⟨hx, hx⟩ b b b b' hb hb hb hb'
    have h2 : gm (𝟙 X) x _ ((L i).g b b) = 1 := mul_eq_left.1 ((hL i).coc x b b b hb hb hb)
    rw [hdiag i b x hb, _root_.one_mul, h2, _root_.one_mul] at h1
    exact h1
  have hg := gm_sigmaGlue_g W L w hL
  refine ⟨sigmaGlue W L w hL, ⟨?_, ?_, ?_⟩, fun i ↦ ⟨fun p b ↦ res (le_inf (le_inf
    (inf_le_right.trans (inf_le_left.trans ((hL p.1).le p.2))) inf_le_left) inf_le_right) (w p.1 i p.2 b), ?_⟩⟩
  · refine eq_top_iff.2 fun x _ ↦ TopologicalSpace.Opens.mem_iSup.2 ?_
    obtain ⟨i, hi⟩ := hW x
    obtain ⟨a, ha⟩ := (hL i).cov x hi
    exact ⟨⟨i, a⟩, ha⟩
  · intro p
    refine unit_ext fun x hx ↦ ?_
    rw [gm_res (𝟙 X) x _ hx, map_one, hg x p p hx hx, hdiag p.1 p.2 x hx]
  · intro p q r
    refine unit_ext fun x hx ↦ ?_
    rw [map_mul, gm_res (𝟙 X) x _ hx, gm_res (𝟙 X) x _ hx, gm_res (𝟙 X) x _ hx,
      hg x p q hx.1.1 hx.1.2, hg x q r hx.1.2 hx.2, hg x p r hx.1.1 hx.2]
    exact hcoc _ _ _ x _ _ _ hx.1.1 hx.1.2 hx.2
  · intro x hx p p' b b' hp hp' hb hb'
    beta_reduce
    erw [gm_res (𝟙 X) x _ (show x ∈ W i ⊓ ((sigmaGlue W L w hL).U p ⊓ (L i).U b) from ⟨hx, hp, hb⟩),
      gm_res (𝟙 X) x _ (show x ∈ W i ⊓ ((sigmaGlue W L w hL).U p' ⊓ (L i).U b') from ⟨hx, hp', hb'⟩),
      hg x p p' hp hp', hgi i x b b' hb hb' hx, hcoc _ _ _ x _ _ _ hp hb hb', hcoc _ _ _ x _ _ _ hp hp' hb']

end GlobalTheory.PicGlue
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleGlueOfOpenCoverCocycle =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoPullOfIsLineBundleIsoOnOpen =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoPullOfIsLineBundleIsoOnOpen", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.WhiskerLeftEqLift\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem isoOn_gm {X Z : Scheme.{0}} {W : X.Opens} {L M : LB X} {w : Cmp W L M} (hw : IsoOn W L M w) (r : Z ⟶ X)
    (y : Z) {a a' : L.ι} {b b' : M.ι} (h0 : r y ∈ W) (ha : r y ∈ L.U a) (ha' : r y ∈ L.U a') (hb : r y ∈ M.U b)
    (hb' : r y ∈ M.U b') :
    gm r y _ (w a b) * gm r y _ (M.g b b') = gm r y _ (L.g a a') * gm r y _ (w a' b') := by
  have h1 : (W ⊓ (L.U a ⊓ M.U b)) ⊓ (W ⊓ (L.U a' ⊓ M.U b')) ≤ W ⊓ (L.U a ⊓ M.U b) := inf_le_left
  have h2 : (W ⊓ (L.U a ⊓ M.U b)) ⊓ (W ⊓ (L.U a' ⊓ M.U b')) ≤ M.U b ⊓ M.U b' :=
    le_inf (inf_le_left.trans (inf_le_right.trans inf_le_right)) (inf_le_right.trans (inf_le_right.trans inf_le_right))
  have h3 : (W ⊓ (L.U a ⊓ M.U b)) ⊓ (W ⊓ (L.U a' ⊓ M.U b')) ≤ L.U a ⊓ L.U a' :=
    le_inf (inf_le_left.trans (inf_le_right.trans inf_le_left)) (inf_le_right.trans (inf_le_right.trans inf_le_left))
  have h4 : (W ⊓ (L.U a ⊓ M.U b)) ⊓ (W ⊓ (L.U a' ⊓ M.U b')) ≤ W ⊓ (L.U a' ⊓ M.U b') := inf_le_right
  have key : ∀ (T : Scheme.{0}) (f : T ⟶ X) (t : T), f t ∈ (W ⊓ (L.U a ⊓ M.U b)) ⊓ (W ⊓ (L.U a' ⊓ M.U b')) →
      gm f t _ (res h1 (w a b) * res h2 (M.g b b')) = gm f t _ (w a b) * gm f t _ (M.g b b') ∧
      gm f t _ (res h3 (L.g a a') * res h4 (w a' b')) = gm f t _ (L.g a a') * gm f t _ (w a' b') :=
    fun T f t ht ↦ ⟨(map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res f t h1 ht _) (gm_res f t h2 ht _)),
      (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res f t h3 ht _) (gm_res f t h4 ht _))⟩
  have e : res h1 (w a b) * res h2 (M.g b b') = res h3 (L.g a a') * res h4 (w a' b') :=
    unit_ext fun x hx ↦ (key X (𝟙 X) x hx).1.trans ((hw x (h1 hx).1 a a' b b' (h3 hx).1 (h3 hx).2 (h2 hx).1 (h2 hx).2).trans
      (key X (𝟙 X) x hx).2.symm)
  have hm : r y ∈ (W ⊓ (L.U a ⊓ M.U b)) ⊓ (W ⊓ (L.U a' ⊓ M.U b')) := ⟨⟨h0, ha, hb⟩, ⟨h0, ha', hb'⟩⟩
  exact (key Z r y hm).1.symm.trans ((congrArg (gm r y _) e).trans (key Z r y hm).2)

theorem lbIso_pull_of_isoOn (X Z : Scheme.{0}) (W : X.Opens) (L M : LB X) (w : Cmp W L M) (r : Z ⟶ X)
    (hw : IsoOn W L M w) (hr : ∀ z, r z ∈ W) : LBIso (L.pull r) (M.pull r) := by
  have le : ∀ p : (PUnit → M.ι) × (PUnit → L.ι), (M.pull r).U p.1 ⊓ (L.pull r).U p.2 ≤
      r ⁻¹ᵁ (W ⊓ (L.U (p.2 PUnit.unit) ⊓ M.U (p.1 PUnit.unit))) :=
    fun p y hy ↦ ⟨hr y, mem_pull.1 hy.2, mem_pull.1 hy.1⟩
  refine ⟨⟨fun p ↦ (res (le p) (pullU r _ (w (p.2 PUnit.unit) (p.1 PUnit.unit))))⁻¹⟩, fun p q ↦ unit_ext fun y hy ↦ ?_⟩
  have val : ∀ p : (PUnit → M.ι) × (PUnit → L.ι), y ∈ (M.pull r).U p.1 ⊓ (L.pull r).U p.2 →
      gm (𝟙 Z) y _ (res (le p) (pullU r _ (w (p.2 PUnit.unit) (p.1 PUnit.unit))))⁻¹ =
        (gm r y _ (w (p.2 PUnit.unit) (p.1 PUnit.unit)))⁻¹ := fun p hp ↦
    (map_inv _ _).trans (congrArg (·⁻¹) ((gm_res (𝟙 Z) y (le p) hp _).trans
      ((gm_pull (𝟙 Z) r y _ (le p hp) _).trans (by rw [Category.id_comp]))))
  have hM := gm_pull_g M r (𝟙 Z) y p.1 q.1 hy.1.1 hy.2.1
  have hL := gm_pull_g L r (𝟙 Z) y p.2 q.2 hy.1.2 hy.2.2
  rw [Category.id_comp] at hM hL
  have hd := gm_div (L.pull r) (M.pull r) (𝟙 Z) y p q hy
  have k := isoOn_gm hw r y (hr y) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2.2) (mem_pull.1 hy.1.1) (mem_pull.1 hy.2.1)
  refine (gm_res (𝟙 Z) y inf_le_left hy _).trans ((val p hy.1).trans (Eq.symm ?_))
  refine (map_mul _ _ _).trans ?_
  refine (congrArg₂ (· * ·) (hd.trans (congrArg₂ (fun u v ↦ u * v⁻¹) hM hL))
    ((gm_res (𝟙 Z) y inf_le_right hy _).trans (val q hy.2))).trans ?_
  rw [eq_mul_inv_of_mul_eq k]
  simp only [mul_inv_rev, inv_inv]
  ac_rfl

end GlobalTheory.PicGlue
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoPullOfIsLineBundleIsoOnOpen =====
