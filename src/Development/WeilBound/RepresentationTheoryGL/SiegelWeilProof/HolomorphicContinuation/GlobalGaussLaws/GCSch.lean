module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussLaw
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussA
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DifferenceQuotientIsometryExchangeAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzCexpNegForm
import Mathlib.Tactic.Linter.Style

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.InvNormSmulMemSphere, Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GCSchA, Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GCSchB, Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GCSch

-- ===== clump member: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.InvNormSmulMemSphere =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.InvNormSmulMemSphere", "h": "module\n\npublic import Mathlib.Analysis.CStarAlgebra.Classes\npublic import Mathlib.Analysis.InnerProductSpace.Basic\npublic import Mathlib.LinearAlgebra.FiniteDimensional.Defs\npublic import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\npublic import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps\n\n"}
section -- clump:auto
@[expose] public section

namespace UpperTheory.Reformulated.B.P6.r24a

theorem quadratic_form_smul_re {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Q : V →L[ℝ] V →L[ℝ] ℂ) (c : ℝ) (x : V) :
    (Q (c • x) (c • x)).re = c ^ 2 * (Q x x).re := by
  simp only [map_smul, ContinuousLinearMap.smul_apply, Complex.smul_re, smul_eq_mul]
  ring

theorem inv_norm_smul_mem_sphere {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (x : V) (hx : x ≠ 0) : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : V) 1 := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']

theorem PositivityTheory.Rg.Sw.Glob.GCSchH.coercive_of_pos :
    ∀ {V : Type} [inst : NormedAddCommGroup V] [inst_1 : NormedSpace ℝ V] [FiniteDimensional ℝ V] (Q : V →L[ℝ] V →L[ℝ] ℂ), (∀ (x : V), x ≠ OfNat.ofNat (nat_lit 0) → OfNat.ofNat (nat_lit 0) < (DFunLike.coe (DFunLike.coe Q x) x).re) → ∃ (κ : ℝ), OfNat.ofNat (nat_lit 0) < κ ∧ ∀ (x : V), κ * ‖x‖ ^ OfNat.ofNat (nat_lit 2) ≤ (DFunLike.coe (DFunLike.coe Q x) x).re := by
  intro V _ _ _ Q hQ
  have hcont : Continuous fun x : V => (Q x x).re :=
    Complex.continuous_re.comp (Q.continuous.clm_apply continuous_id)
  by_cases hne : (Metric.sphere (0 : V) 1).Nonempty
  · obtain ⟨x0, hx0, hmin⟩ :=
      (isCompact_sphere (0 : V) 1).exists_isMinOn hne hcont.continuousOn
    have hx0ne : x0 ≠ 0 := by
      intro h
      rw [h, mem_sphere_zero_iff_norm, norm_zero] at hx0
      exact zero_ne_one hx0
    refine ⟨(Q x0 x0).re, hQ x0 hx0ne, fun x => ?_⟩
    by_cases hx : x = 0
    · subst hx
      simp
    · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
      obtain ⟨y, hyd⟩ : ∃ y : V, y = ‖x‖⁻¹ • x := ⟨_, rfl⟩
      have hy : y ∈ Metric.sphere (0 : V) 1 := hyd ▸ inv_norm_smul_mem_sphere x hx
      have h1 : (Q x0 x0).re ≤ (Q y y).re := hmin hy
      have h2 : ‖x‖ • y = x := by
        rw [hyd, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
      have h3 : (Q x x).re = ‖x‖ ^ 2 * (Q y y).re := by
        have := quadratic_form_smul_re Q ‖x‖ y
        rw [h2] at this
        exact this
      rw [h3, mul_comm (‖x‖ ^ 2)]
      exact mul_le_mul_of_nonneg_right h1 (by positivity)
  · refine ⟨1, one_pos, fun x => ?_⟩
    have hx : x = 0 := by
      by_contra hx
      exact hne ⟨_, inv_norm_smul_mem_sphere x hx⟩
    subst hx
    simp

end UpperTheory.Reformulated.B.P6.r24a
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.InvNormSmulMemSphere =====

-- ===== clump member: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GCSchA =====
-- clump-header: {"m": "Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GCSchA", "h": "module\n\npublic import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussLaw\npublic import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.InvNormSmulMemSphere\npublic import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussA\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GCSchH

variable {m n : ℕ}

theorem trace_gramB (Z : Matrix (Fin n) (Fin n) ℂ) (ε : Fin m → Bool) (b : Bool) (u : Fin m → Fin n → ℂ) :
    (Z * gramB ε b u).trace = ∑ a ∈ Finset.univ.filter (fun a => ε a = b), star (u a) ⬝ᵥ (Zᵀ *ᵥ u a) := by
  set S := Finset.univ.filter (fun a => ε a = b)
  have hG : ∀ i j, gramB ε b u j i = ∑ a ∈ S, star (u a j) * u a i := fun i j => GaussH.gramB_apply ε b u j i
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, hG, Finset.mul_sum, dotProduct, mulVec,
    Matrix.transpose_apply, Pi.star_apply]
  calc _ = ∑ i, ∑ a ∈ S, ∑ j, Z i j * (star (u a j) * u a i) := Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ a ∈ S, ∑ i, ∑ j, Z i j * (star (u a j) * u a i) := Finset.sum_comm
    _ = ∑ a ∈ S, ∑ j, ∑ i, Z i j * (star (u a j) * u a i) := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem im_quad (W : Matrix (Fin n) (Fin n) ℂ) (y : Fin n → ℂ) :
    (star y ⬝ᵥ (W *ᵥ y)).im = (star y ⬝ᵥ (((-(Complex.I / 2)) • (W - Wᴴ)) *ᵥ y)).re := by
  have hs : star (star y ⬝ᵥ (W *ᵥ y)) = star y ⬝ᵥ (Wᴴ *ᵥ y) := by
    rw [Matrix.star_dotProduct, Matrix.star_mulVec, star_star, ← Matrix.dotProduct_mulVec]
  rw [Matrix.smul_mulVec, dotProduct_smul, Matrix.sub_mulVec, dotProduct_sub, ← hs]
  set s := star y ⬝ᵥ (W *ᵥ y)
  simp only [smul_eq_mul, Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im, Complex.neg_re, Complex.neg_im, Complex.div_re, Complex.div_im, Complex.I_re, Complex.I_im]
  norm_num
  ring

alias coercive_of_pos := _root_.UpperTheory.Reformulated.B.P6.r24a.PositivityTheory.Rg.Sw.Glob.GCSchH.coercive_of_pos

end PositivityTheory.Rg.Sw.Glob.GCSchH
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GCSchA =====

-- ===== clump member: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GCSchB =====
-- clump-header: {"m": "Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GCSchB", "h": "module\n\npublic import Mathlib.Analysis.CStarAlgebra.Classes\npublic import Mathlib.Analysis.InnerProductSpace.Basic\npublic import Mathlib.LinearAlgebra.Matrix.PosDef\npublic import Mathlib.Topology.Algebra.Module.FiniteDimension\npublic import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.LocallyConvex.AbsConvexOpen\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\npublic import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GCSchA\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GCSchH

variable {m n : ℕ}

def qF (S S' : Finset (Fin m)) (c : ℝ) (Z Z' : Matrix (Fin n) (Fin n) ℂ) (u v : Fin m → Fin n → ℂ) : ℂ :=
  -(Complex.I * c * ∑ a ∈ S, star (u a) ⬝ᵥ (Zᵀ *ᵥ v a) - Complex.I * c * ∑ a ∈ S', star (u a) ⬝ᵥ (Z'ᵀ *ᵥ v a))

def qL (S S' : Finset (Fin m)) (c : ℝ) (Z Z' : Matrix (Fin n) (Fin n) ℂ) :
    (Fin m → Fin n → ℂ) →ₗ[ℝ] (Fin m → Fin n → ℂ) →ₗ[ℝ] ℂ :=
  LinearMap.mk₂ ℝ (qF S S' c Z Z')
    (fun u₁ u₂ v => by
      simp only [qF, Pi.add_apply, star_add, add_dotProduct, Finset.sum_add_distrib]; ring)
    (fun r u v => by
      simp only [qF, Pi.smul_apply, star_smul, star_trivial, smul_dotProduct, Complex.real_smul, ← Finset.mul_sum]
      ring)
    (fun u v₁ v₂ => by
      simp only [qF, Pi.add_apply, Matrix.mulVec_add, dotProduct_add, Finset.sum_add_distrib]; ring)
    (fun r u v => by
      simp only [qF, Pi.smul_apply, Matrix.mulVec_smul, dotProduct_smul, Complex.real_smul, ← Finset.mul_sum]
      ring)

def qB (S S' : Finset (Fin m)) (c : ℝ) (Z Z' : Matrix (Fin n) (Fin n) ℂ) :
    (Fin m → Fin n → ℂ) →L[ℝ] (Fin m → Fin n → ℂ) →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : ((Fin m → Fin n → ℂ) →ₗ[ℝ] ℂ) ≃ₗ[ℝ] _).toLinearMap ∘ₗ qL S S' c Z Z')

theorem qB_apply (S S' : Finset (Fin m)) (c : ℝ) (Z Z' : Matrix (Fin n) (Fin n) ℂ) (u v : Fin m → Fin n → ℂ) :
    qB S S' c Z Z' u v = qF S S' c Z Z' u v := rfl

theorem re_I_mul (c : ℝ) (z : ℂ) : (Complex.I * c * z).re = -(c * z.im) := by
  simp [Complex.mul_re, Complex.mul_im]

theorem quad_nonneg {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.PosDef) (y : Fin n → ℂ) : 0 ≤ (star y ⬝ᵥ (P *ᵥ y)).re := (Complex.nonneg_iff.mp (hP.posSemidef.dotProduct_mulVec_nonneg y)).1

theorem quad_pos {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.PosDef) {y : Fin n → ℂ} (hy : y ≠ 0) :
    0 < (star y ⬝ᵥ (P *ᵥ y)).re := (Complex.pos_iff.mp (hP.dotProduct_mulVec_pos hy)).1

end PositivityTheory.Rg.Sw.Glob.GCSchH
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GCSchB =====

-- ===== clump member: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GCSch =====
-- clump-header: {"m": "Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GCSch", "h": "module\n\npublic import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DifferenceQuotientIsometryExchangeAlt\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzCexpNegForm\npublic import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GCSchA\npublic import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GCSchB\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob

open GCSchH

theorem gCSch : GCSch := by
  intro m n ε t c hc htc Z Z' hZ hZ'
  set S := Finset.univ.filter (fun a => epsT t ε a = true) with hS
  set S' := Finset.univ.filter (fun a => epsT t ε a = false) with hS'
  set B := qB S S' c Z Z' with hB
  have hgC : gC ε t c Z Z' = fun u => Complex.exp (-(B u u)) := by
    funext u
    simp only [gC, hB, qB_apply, qF, neg_neg, trace_gramB]
    rfl
  have hP1 : ((-(Complex.I / 2)) • (Zᵀ - Zᵀᴴ)).PosDef := by
    have h := hZ.transpose
    rwa [Matrix.transpose_smul, Matrix.transpose_sub, Matrix.conjTranspose_transpose] at h
  have hP2 : ((-(Complex.I / 2)) • (-Z'ᵀ - (-Z'ᵀ)ᴴ)).PosDef := by
    have h := hZ'.transpose
    rw [Matrix.conjTranspose_conjTranspose, Matrix.transpose_smul, Matrix.transpose_sub,
      Matrix.conjTranspose_transpose] at h
    rwa [Matrix.conjTranspose_neg, sub_neg_eq_add, neg_add_eq_sub]
  have hre : ∀ u : Fin m → Fin n → ℂ, (B u u).re = c * (∑ a ∈ S, (star (u a) ⬝ᵥ
      (((-(Complex.I / 2)) • (Zᵀ - Zᵀᴴ)) *ᵥ u a)).re + ∑ a ∈ S', (star (u a) ⬝ᵥ
      (((-(Complex.I / 2)) • (-Z'ᵀ - (-Z'ᵀ)ᴴ)) *ᵥ u a)).re) := by
    intro u
    rw [hB, qB_apply, qF, Complex.neg_re, Complex.sub_re, re_I_mul, re_I_mul, Complex.im_sum, Complex.im_sum]
    have e2 : ∀ a, (star (u a) ⬝ᵥ (Z'ᵀ *ᵥ u a)).im = -(star (u a) ⬝ᵥ ((-Z'ᵀ) *ᵥ u a)).im := by
      intro a; rw [Matrix.neg_mulVec, dotProduct_neg, Complex.neg_im, neg_neg]
    simp only [e2, Finset.sum_neg_distrib, im_quad]
    ring
  have hpos : ∀ u : Fin m → Fin n → ℂ, u ≠ 0 → 0 < (B u u).re := by
    intro u hu
    obtain ⟨a, ha⟩ := Function.ne_iff.1 hu
    rw [hre]
    apply mul_pos hc
    have n1 : 0 ≤ ∑ a ∈ S, (star (u a) ⬝ᵥ (((-(Complex.I / 2)) • (Zᵀ - Zᵀᴴ)) *ᵥ u a)).re :=
      Finset.sum_nonneg fun a _ => quad_nonneg hP1 _
    have n2 : 0 ≤ ∑ a ∈ S', (star (u a) ⬝ᵥ (((-(Complex.I / 2)) • (-Z'ᵀ - (-Z'ᵀ)ᴴ)) *ᵥ u a)).re :=
      Finset.sum_nonneg fun a _ => quad_nonneg hP2 _
    cases hb : epsT t ε a
    · have haS : a ∈ S' := by simp [hS', hb]
      have p2 := Finset.sum_pos' (fun a _ => quad_nonneg hP2 (u a)) ⟨a, haS, quad_pos hP2 ha⟩
      linarith
    · have haS : a ∈ S := by simp [hS, hb]
      have p1 := Finset.sum_pos' (fun a _ => quad_nonneg hP1 (u a)) ⟨a, haS, quad_pos hP1 ha⟩
      linarith
  obtain ⟨κ, hκ, hco⟩ := coercive_of_pos B hpos
  obtain ⟨g, hg, -⟩ := GlobalTheory.GaussComplexForm.exists_schwartz_cexp_neg_form _ B κ hκ hco
  refine ⟨g, ?_⟩
  rw [hgC]
  funext u
  exact hg u

theorem gZSch : GZSch := by
  intro m n ε t c hc htc Z hZ
  show IsSch (gC ε t c Z Zᴴ)
  exact gCSch m n ε t c hc htc Z Zᴴ hZ (by rw [Matrix.conjTranspose_conjTranspose]; exact hZ)

end PositivityTheory.Rg.Sw.Glob
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GCSch =====
