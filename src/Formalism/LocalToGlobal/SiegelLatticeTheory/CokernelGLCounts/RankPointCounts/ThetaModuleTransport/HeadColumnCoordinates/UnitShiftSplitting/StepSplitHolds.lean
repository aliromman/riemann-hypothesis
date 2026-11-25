module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.SumIndL
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.FormSplitP
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.SecondCoeffSecondIdempotent
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.ZzMinusSecondProjTranspose
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.SecondProjConjApply
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumA
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.SharpEquivApply
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.SecondProjConjEqFirstProj

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.AdeleInfiniteComponentApply, Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.ConjMapSecondProj, Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.ComponentsOfSecondComponentEq, Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.AsmCompat, Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.GammaOneNonempty, Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.SecondIsoComponentLinearOf, Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.SecondProjUniformizerMul, Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.FormSplit, Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.StepSplitHolds

-- ===== clump member: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.AdeleInfiniteComponentApply =====
-- clump-header: {"m": "Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.AdeleInfiniteComponentApply", "h": "module\n\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.SumIndL\nimport Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.CompOfMemR\nimport Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.ExistsUnitShift\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumA\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

namespace Formalism.L2.SG.LocalCountModules.AlgGSplit

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

def p1 (g : SplitG M.L) : E →+* F := (RingHom.fst F F).comp g.e.toRingEquiv.toRingHom

def p2 (g : SplitG M.L) : E →+* F := (RingHom.snd F F).comp g.e.toRingEquiv.toRingHom

theorem adeleInfiniteComponent_apply (x : E) : p1 g x = (g.e x).1 := rfl
theorem adele_ext_components (x : E) : p2 g x = (g.e x).2 := rfl

theorem map_inv_of {K : Type} [CommRing K] {n : Type} [Fintype n] [DecidableEq n] (f : E →+* K)
    (A : Matrix n n E) (hA : IsUnit A.det) : (A⁻¹).map f = (A.map f)⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hA, Matrix.map_one _ (map_zero f) (map_one f)]

theorem inv_last {K : Type} [CommRing K] (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    A⁻¹ (Fin.last r) (Fin.last r) = Ring.inverse A.det * (A.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last]
  simp

theorem kap_common {Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hk : KapEq Zh₁ Zh₂)
    (h₁ : IsUnit Zh₁.det) (h₂ : IsUnit Zh₂.det) :
    Zh₁⁻¹ (Fin.last r) (Fin.last r) = Zh₂⁻¹ (Fin.last r) (Fin.last r) := by
  rw [inv_last, inv_last]
  obtain ⟨u₁, hu₁⟩ := h₁
  obtain ⟨u₂, hu₂⟩ := h₂
  unfold KapEq at hk
  rw [← hu₁, ← hu₂] at hk ⊢
  simp only [Ring.inverse_unit]
  apply (u₁ * u₂).isUnit.mul_left_cancel
  push_cast
  calc (u₁ : E) * u₂ * (↑u₁⁻¹ * (Zh₁.submatrix Fin.castSucc Fin.castSucc).det)
      = u₂ * (Zh₁.submatrix Fin.castSucc Fin.castSucc).det * (u₁ * ↑u₁⁻¹) := by ring
    _ = u₂ * (Zh₁.submatrix Fin.castSucc Fin.castSucc).det := by rw [Units.mul_inv, mul_one]
    _ = u₁ * (Zh₂.submatrix Fin.castSucc Fin.castSucc).det := hk.symm
    _ = u₁ * (Zh₂.submatrix Fin.castSucc Fin.castSucc).det * (u₂ * ↑u₂⁻¹) := by rw [Units.mul_inv, mul_one]
    _ = (u₁ : E) * u₂ * (↑u₂⁻¹ * (Zh₂.submatrix Fin.castSucc Fin.castSucc).det) := by ring

variable (hs : M.split = some g)
include hs

theorem zzMinus_firstProj (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    (ZZm g Zh T T').map (p1 g) = (g.q : F)⁻¹ • Zh.map (p1 g) := by
  ext b a
  simp only [ZZm, Matrix.map_apply, Matrix.add_apply, Matrix.of_apply, map_add (f := _), Matrix.smul_apply,
    smul_eq_mul, adeleInfiniteComponent_apply]
  rw [zz_comp hs, e_cor]
  simp only [ind, AlgEquiv.apply_symm_apply]
  split_ifs <;> ring

theorem zzMinus_secondProj (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    (ZZm g Zh T T').map (p2 g) = -(g.q : F)⁻¹ • (Zh.map (p2 g)).transpose := by
  ext b a
  simp only [ZZm, Matrix.map_apply, Matrix.add_apply, Matrix.of_apply, map_add (f := _), Matrix.smul_apply,
    smul_eq_mul, adele_ext_components, Matrix.transpose_apply]
  rw [zz_comp hs, e_cor]
  simp only [ind, AlgEquiv.apply_symm_apply]
  split_ifs <;> ring

theorem det_map_unit {n : Type} [Fintype n] [DecidableEq n] (f : E →+* F) (A : Matrix n n E)
    (hA : IsUnit A.det) : IsUnit (A.map f).det := by
  have := hA.map f
  rwa [RingHom.map_det] at this

theorem zm_unit {Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hZh : IsUnit Zh.det) (T T' : F) :
    IsUnit (ZZm g Zh T T').det := by
  apply _root_.Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork.unit_zzm <;> assumption

theorem inv_smul_q {n : Type} [Fintype n] [DecidableEq n] (c : F) (hc : c ≠ 0) (X : Matrix n n F)
    (hX : IsUnit X.det) : (c⁻¹ • X)⁻¹ = c • X⁻¹ := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc, one_smul, Matrix.nonsing_inv_mul _ hX]

theorem inv_smul_qT {n : Type} [Fintype n] [DecidableEq n] (c : F) (hc : c ≠ 0) (X : Matrix n n F)
    (hX : IsUnit X.det) : (-c⁻¹ • X.transpose)⁻¹ = -c • (X⁻¹).transpose := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, neg_mul_neg, mul_inv_cancel₀ hc, one_smul,
    ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hX, Matrix.transpose_one]

theorem lastCoordinate_firstProj {Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hZh : IsUnit Zh.det) (T T' : F)
    (l : Fin (r + 1) → M.R) :
    p1 g (laG (ZZm g Zh T T') l) = ∑ b, (g.q : F) * (Zh.map (p1 g))⁻¹ (Fin.last r) b * p1 g (l b) := by
  have hq := q_ne g

  simp only [laG, Matrix.mulVec, dotProduct, map_sum, map_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h := congrFun (congrFun (map_inv_of (p1 g) _ (zm_unit hs hZh T T')) (Fin.last r)) b
  rw [Matrix.map_apply] at h
  rw [h, zzMinus_firstProj hs, inv_smul_q hs _ hq _ (det_map_unit hs (p1 g) Zh hZh), Matrix.smul_apply, smul_eq_mul]

theorem lastCoordinate_secondProj {Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hZh : IsUnit Zh.det) (T T' : F)
    (l : Fin (r + 1) → M.R) :
    p2 g (laG (ZZm g Zh T T') l) = ∑ b, -(g.q : F) * (Zh.map (p2 g))⁻¹ b (Fin.last r) * p2 g (l b) := by
  have hq := q_ne g

  simp only [laG, Matrix.mulVec, dotProduct, map_sum, map_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h := congrFun (congrFun (map_inv_of (p2 g) _ (zm_unit hs hZh T T')) (Fin.last r)) b
  rw [Matrix.map_apply] at h
  rw [h, zzMinus_secondProj hs, inv_smul_qT hs _ hq _ (det_map_unit hs (p2 g) Zh hZh), Matrix.smul_apply, smul_eq_mul,
    Matrix.transpose_apply]

theorem lambda_firstProj {Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hZh : IsUnit Zh.det) (y : Fin (r + 1) → E) :
    p1 g (lamC Zh y) = ∑ b, (Zh.map (p1 g))⁻¹ (Fin.last r) b * p1 g (y b) := by

  simp only [lamC, Matrix.mulVec, dotProduct, map_sum, map_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← map_inv_of (p1 g) _ hZh, Matrix.map_apply]

theorem lambda_secondProj {Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hZh : IsUnit Zh.det) (y : Fin (r + 1) → E) :
    p2 g (lamC Zh y) = ∑ b, (Zh.map (p2 g))⁻¹ (Fin.last r) b * p2 g (y b) := by

  simp only [lamC, Matrix.mulVec, dotProduct, map_sum, map_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← map_inv_of (p2 g) _ hZh, Matrix.map_apply]

theorem firstProj_conj_split (x : E) : p1 g ((M.L.cj : E →+* E) x) = p2 g x := by
  rw [adeleInfiniteComponent_apply, adele_ext_components, e_cjR]

theorem secondProj_conj_split (x : E) : p2 g ((M.L.cj : E →+* E) x) = p1 g x := by
  rw [adeleInfiniteComponent_apply, adele_ext_components, e_cjR]

theorem lambdaStar_firstProj {Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hZh : IsUnit Zh.det) (y : Fin (r + 1) → E) :
    p1 g (lamStarC (M.L.cj : E →+* E) Zh y) = ∑ b, (Zh.map (p2 g))⁻¹ b (Fin.last r) * p1 g (y b) := by

  simp only [lamStarC, map_sum, map_mul, firstProj_conj_split hs]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← map_inv_of (p2 g) _ hZh, Matrix.map_apply]

theorem lambdaStar_secondProj {Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hZh : IsUnit Zh.det) (y : Fin (r + 1) → E) :
    p2 g (lamStarC (M.L.cj : E →+* E) Zh y) = ∑ b, (Zh.map (p1 g))⁻¹ b (Fin.last r) * p2 g (y b) := by

  simp only [lamStarC, map_sum, map_mul, secondProj_conj_split hs]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← map_inv_of (p1 g) _ hZh, Matrix.map_apply]

theorem corner_inverse_firstProj {Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hZh : IsUnit Zh.det) :
    p1 g (Zh⁻¹ (Fin.last r) (Fin.last r)) = (Zh.map (p1 g))⁻¹ (Fin.last r) (Fin.last r) := by
  rw [← map_inv_of (p1 g) _ hZh, Matrix.map_apply]

theorem corner_inverse_secondProj {Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hZh : IsUnit Zh.det) :
    p2 g (Zh⁻¹ (Fin.last r) (Fin.last r)) = (Zh.map (p2 g))⁻¹ (Fin.last r) (Fin.last r) := by
  rw [← map_inv_of (p2 g) _ hZh, Matrix.map_apply]

end Formalism.L2.SG.LocalCountModules.AlgGSplit
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.AdeleInfiniteComponentApply =====

-- ===== clump member: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.ConjMapSecondProj =====
-- clump-header: {"m": "Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.ConjMapSecondProj", "h": "module\n\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.AdeleInfiniteComponentApply\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumA\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

namespace Formalism.L2.SG.LocalCountModules.AlgGSplit

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ} (hs : M.split = some g)

def dl (r : ℕ) (b : Fin (r + 1)) : F := if b = Fin.last r then 1 else 0

theorem e_ueq (η : M.R) (l : Fin (r + 1) → M.R) (b : Fin (r + 1)) :
    g.e ((((η • (eV r : Fin (r + 1) → M.R) + q2 hs • l) : Fin (r + 1) → M.R) b : M.R) : E) =
      (p1 g η * dl r b, p2 g η * dl r b + (g.q : F) * p2 g (l b)) := by
  have he : g.e (((eV r : Fin (r + 1) → M.R) b : M.R) : E) = ((dl r b : F), (dl r b : F)) := by
    by_cases hb : b = Fin.last r
    · subst hb
      rw [show (((eV r : Fin (r + 1) → M.R) (Fin.last r) : M.R) : E) = 1 by simp [eV], map_one]
      simp only [dl, ite_true]
      rfl
    · rw [show (((eV r : Fin (r + 1) → M.R) b : M.R) : E) = 0 by simp [eV, hb], map_zero]
      simp only [dl, ite_eq_right hb]
      rfl
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, AddMemClass.coe_add, MulMemClass.coe_mul, map_add (f := _),
    map_mul, he, embedding_uniformizer]
  ext
  · simp [p1]
  · simp [p2]

theorem conj_map_firstProj (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : (Zh.map M.L.cj).map (p1 g) = Zh.map (p2 g) := by
  ext i j
  simp [p1, p2, g.e_cj]

theorem conj_map_secondProj (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : (Zh.map M.L.cj).map (p2 g) = Zh.map (p1 g) := by
  ext i j
  simp [p1, p2, g.e_cj]

theorem sum_dl (x : Fin (r + 1) → F) : ∑ b, x b * dl r b = x (Fin.last r) := by
  simp [dl, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']

end Formalism.L2.SG.LocalCountModules.AlgGSplit
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.ConjMapSecondProj =====

-- ===== clump member: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.ComponentsOfSecondComponentEq =====
-- clump-header: {"m": "Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.ComponentsOfSecondComponentEq", "h": "module\n\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.ConjMapSecondProj\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumA\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

namespace Formalism.L2.SG.LocalCountModules.AlgGSplit

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ} (hs : M.split = some g)

def pdat (g : SplitG M.L) (k : E) (η : M.R) (la : E) (η' : M.R) (la' : E) : (E × E) × (E × E) :=
  ((g.e.symm (p1 g η, p1 g η'), g.e.symm (p2 g k * p2 g η - p2 g la, p1 g k * p2 g η' - p2 g la')),
    (g.e.symm (p1 g k * p1 g η - p1 g la, p2 g k * p1 g η' - p1 g la'), g.e.symm (p2 g η, p2 g η')))

theorem components_of_firstComponent_eq {Y : Ix r → M.L.O} {u : Fin (r + 1) → M.R} (h : cmp1 hs Y = u) (b : Fin (r + 1)) :
    p1 g (Y (Sum.inl b)) = p1 g (u b) ∧
      p1 g (Y (Sum.inl b)) + (g.q : F) * p1 g (Y (Sum.inr b)) = p2 g (u b) := by
  subst h
  have he := e_rOf hs (c1 g (Y (Sum.inl b))) (c1 g (Y (Sum.inr b)))
  have hc : (cmp1 hs Y b : M.R) = rOf hs (c1 g (Y (Sum.inl b))) (c1 g (Y (Sum.inr b))) := rfl
  constructor
  · show (g.e (Y (Sum.inl b) : E)).1 = (g.e ((cmp1 hs Y b : M.R) : E)).1
    rw [hc, he]
    rfl
  · show (g.e (Y (Sum.inl b) : E)).1 + (g.q : F) * (g.e (Y (Sum.inr b) : E)).1 = (g.e ((cmp1 hs Y b : M.R) : E)).2
    rw [hc, he]
    rfl

theorem components_of_secondComponent_eq {Y : Ix r → M.L.O} {u : Fin (r + 1) → M.R} (h : cmp2 hs Y = u) (b : Fin (r + 1)) :
    p2 g (Y (Sum.inl b)) = p1 g (u b) ∧
      p2 g (Y (Sum.inl b)) + (g.q : F) * p2 g (Y (Sum.inr b)) = p2 g (u b) := by
  subst h
  have he := e_rOf hs (c2 g (Y (Sum.inl b))) (c2 g (Y (Sum.inr b)))
  have hc : (cmp2 hs Y b : M.R) = rOf hs (c2 g (Y (Sum.inl b))) (c2 g (Y (Sum.inr b))) := rfl
  constructor
  · show (g.e (Y (Sum.inl b) : E)).2 = (g.e ((cmp2 hs Y b : M.R) : E)).1
    rw [hc, he]
    rfl
  · show (g.e (Y (Sum.inl b) : E)).2 + (g.q : F) * (g.e (Y (Sum.inr b) : E)).2 = (g.e ((cmp2 hs Y b : M.R) : E)).2
    rw [hc, he]
    rfl

theorem firstProj_unit_vector_eq (η : M.R) (l : Fin (r + 1) → M.R) (b : Fin (r + 1)) :
    p1 g ((((η • (eV r : Fin (r + 1) → M.R) + q2 hs • l) : Fin (r + 1) → M.R) b : M.R) : E) = p1 g η * dl r b := by
  show (g.e _).1 = _
  rw [e_ueq hs η l b]

theorem secondProj_unit_vector_eq (η : M.R) (l : Fin (r + 1) → M.R) (b : Fin (r + 1)) :
    p2 g ((((η • (eV r : Fin (r + 1) → M.R) + q2 hs • l) : Fin (r + 1) → M.R) b : M.R) : E) =
      p2 g η * dl r b + (g.q : F) * p2 g (l b) := by
  show (g.e _).2 = _
  rw [e_ueq hs η l b]

theorem dl_last (r : ℕ) : dl (F := F) r (Fin.last r) = 1 := by
  simp [dl]

theorem firstProj_algebraMap_split (a : F) : p1 g (algebraMap F E a) = a := by
  show (g.e (algebraMap F E a)).1 = a
  rw [AlgEquiv.commutes]
  rfl
theorem secondProj_algebraMap_split (a : F) : p2 g (algebraMap F E a) = a := by
  show (g.e (algebraMap F E a)).2 = a
  rw [AlgEquiv.commutes]
  rfl

variable {Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hZh : IsUnit Zh.det) (T T' : F)
  {Y Y' Y'' : Ix r → M.L.O} {η η' : M.R} {l l' : Fin (r + 1) → M.R}
  (h1 : cmp1 hs Y = η • (eV r : Fin (r + 1) → M.R) + q2 hs • l)
  (h2 : cmp2 hs Y = η' • (eV r : Fin (r + 1) → M.R) + q2 hs • l')
  (h3 : cmp1 hs Y'' = l) (h4 : cmp2 hs Y'' = l')
  (hY : ∀ i, (Y i : E) - Y' i = algebraMap F E (g.q : F) * Y'' i)

include hZh h1 h2 h3 h4 hY in
theorem vals :
    (((Y (Sum.inl (Fin.last r)) : E),
        lamStarC (M.L.cj : E →+* E) Zh (fun b => (Y (Sum.inl b) : E) + algebraMap F E (g.q : F) * Y (Sum.inr b))),
      (lamC Zh (fun a => (Y' (Sum.inl a) : E)),
        (Y' (Sum.inl (Fin.last r)) : E) + algebraMap F E (g.q : F) * Y' (Sum.inr (Fin.last r)))) =
      pdat g (Zh⁻¹ (Fin.last r) (Fin.last r)) η (laG (ZZm g Zh T T') l) η'
        (laG (ZZm g (Zh.map M.L.cj) T T') l') := by
  have hZc : IsUnit (Zh.map M.L.cj).det := by
    have := hZh.map (M.L.cj : E →+* E)
    rwa [RingHom.map_det] at this
  have fY := components_of_firstComponent_eq hs h1
  have gY := components_of_secondComponent_eq hs h2
  have fZ := components_of_firstComponent_eq hs h3
  have gZ := components_of_secondComponent_eq hs h4
  have hW1 : ∀ i, p1 g (Y' i) = p1 g (Y i) - (g.q : F) * p1 g (Y'' i) := fun i => by
    have := congrArg (p1 g) (hY i); rw [map_sub, map_mul, firstProj_algebraMap_split] at this; linear_combination -this
  have hW2 : ∀ i, p2 g (Y' i) = p2 g (Y i) - (g.q : F) * p2 g (Y'' i) := fun i => by
    have := congrArg (p2 g) (hY i); rw [map_sub, map_mul, secondProj_algebraMap_split] at this; linear_combination -this
  simp only [firstProj_unit_vector_eq hs, secondProj_unit_vector_eq hs] at fY gY
  simp only [pdat]
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_) <;> simp only <;> apply g.e.injective <;>
    rw [AlgEquiv.apply_symm_apply] <;> refine Prod.ext ?_ ?_ <;> simp only [← adeleInfiniteComponent_apply, ← adele_ext_components]
  · rw [(fY _).1, dl, ite_eq_left rfl, mul_one]
  · rw [(gY _).1, dl, ite_eq_left rfl, mul_one]
  · rw [lambdaStar_firstProj hs hZh, lastCoordinate_secondProj hs hZh, corner_inverse_secondProj hs hZh]
    have e : ∀ b, (Zh.map (p2 g))⁻¹ b (Fin.last r) *
        p1 g ((Y (Sum.inl b) : E) + algebraMap F E (g.q : F) * Y (Sum.inr b)) =
        (Zh.map (p2 g))⁻¹ b (Fin.last r) * p2 g η * dl r b +
          -(-(g.q : F) * (Zh.map (p2 g))⁻¹ b (Fin.last r) * p2 g (l b)) := fun b => by
      rw [map_add (f := _), map_mul, firstProj_algebraMap_split, (fY b).2]; ring
    rw [Finset.sum_congr rfl fun b _ => e b, Finset.sum_add_distrib, Finset.sum_neg_distrib, sum_dl]
    ring
  · rw [lambdaStar_secondProj hs hZh, lastCoordinate_secondProj hs hZc, corner_inverse_firstProj hs hZh, conj_map_secondProj]
    have e : ∀ b, (Zh.map (p1 g))⁻¹ b (Fin.last r) *
        p2 g ((Y (Sum.inl b) : E) + algebraMap F E (g.q : F) * Y (Sum.inr b)) =
        (Zh.map (p1 g))⁻¹ b (Fin.last r) * p2 g η' * dl r b +
          -(-(g.q : F) * (Zh.map (p1 g))⁻¹ b (Fin.last r) * p2 g (l' b)) := fun b => by
      rw [map_add (f := _), map_mul, secondProj_algebraMap_split, (gY b).2]; ring
    rw [Finset.sum_congr rfl fun b _ => e b, Finset.sum_add_distrib, Finset.sum_neg_distrib, sum_dl]
    ring
  · rw [lambda_firstProj hs hZh, lastCoordinate_firstProj hs hZh, corner_inverse_firstProj hs hZh]
    have e : ∀ b, (Zh.map (p1 g))⁻¹ (Fin.last r) b * p1 g (Y' (Sum.inl b) : E) =
        (Zh.map (p1 g))⁻¹ (Fin.last r) b * p1 g η * dl r b +
          -((g.q : F) * (Zh.map (p1 g))⁻¹ (Fin.last r) b * p1 g (l b)) := fun b => by
      rw [hW1, (fY b).1, (fZ b).1]; ring
    rw [Finset.sum_congr rfl fun b _ => e b, Finset.sum_add_distrib, Finset.sum_neg_distrib, sum_dl]
    ring
  · rw [lambda_secondProj hs hZh, lastCoordinate_firstProj hs hZc, corner_inverse_secondProj hs hZh, conj_map_firstProj]
    have e : ∀ b, (Zh.map (p2 g))⁻¹ (Fin.last r) b * p2 g (Y' (Sum.inl b) : E) =
        (Zh.map (p2 g))⁻¹ (Fin.last r) b * p1 g η' * dl r b +
          -((g.q : F) * (Zh.map (p2 g))⁻¹ (Fin.last r) b * p1 g (l' b)) := fun b => by
      rw [hW2, (gY b).1, (gZ b).1]; ring
    rw [Finset.sum_congr rfl fun b _ => e b, Finset.sum_add_distrib, Finset.sum_neg_distrib, sum_dl]
    ring
  · rw [map_add (f := _), map_mul, firstProj_algebraMap_split, hW1, hW1]
    linear_combination (fY (Fin.last r)).2 - (g.q : F) * (fZ (Fin.last r)).2 +
      p2 g η * (dl_last (F := F) r)
  · rw [map_add (f := _), map_mul, secondProj_algebraMap_split, hW2, hW2]
    linear_combination (gY (Fin.last r)).2 - (g.q : F) * (gZ (Fin.last r)).2 +
      p2 g η' * (dl_last (F := F) r)

end Formalism.L2.SG.LocalCountModules.AlgGSplit
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.ComponentsOfSecondComponentEq =====

-- ===== clump member: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.AsmCompat =====
-- clump-header: {"m": "Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.AsmCompat", "h": "module\n\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.ComponentsOfSecondComponentEq\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.FormSplitP\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumA\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

namespace Formalism.L2.SG.LocalCountModules.AlgGSplit

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

def asm (hs : M.split = some g) {T T' : F} {TT : M.R} {Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    {Z Zσ : M.Mat (r + 1)} (h : GHyp M g T T' TT Zh Z Zσ)
    (ab : (DD1 hs Z TT × DD1 hs Z TT × M.R × E) × (DD1 hs Zσ TT × DD1 hs Zσ TT × M.R × E)) :
    DG g Zh T T' × DG g Zh T T' × (E × E) × (E × E) :=
  ((splitH hs h).symm (ab.1.1, ab.2.1), (splitH hs h).symm (ab.1.2.1, ab.2.2.1),
    pdat g (Zh⁻¹ (Fin.last r) (Fin.last r)) ab.1.2.2.1 ab.1.2.2.2 ab.2.2.2.1 ab.2.2.2.2)

abbrev GR (g : SplitG M.L) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :=
  GamRC M.L.O (M.L.cj : E →+* E) (algebraMap F E (g.q : F)) (algebraMap F E ((g.q : F)⁻¹)) Zh
    (algebraMap F E T) (algebraMap F E T')

def GamSubP : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L) (hs : M.split = some g) (r : ℕ) (T T' : F) (TT : M.R)
    (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z Zσ : M.Mat (r + 1)) (h : GHyp M g T T' TT Zh Z Zσ),
    GR g Zh T T' ⊆ asm hs h '' (Gam1 hs Z TT (ZZm g Zh T T') ×ˢ Gam1 hs Zσ TT (ZZm g (Zh.map M.L.cj) T T'))

def GamSupP : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L) (hs : M.split = some g) (r : ℕ) (T T' : F) (TT : M.R)
    (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z Zσ : M.Mat (r + 1)) (h : GHyp M g T T' TT Zh Z Zσ),
    asm hs h '' (Gam1 hs Z TT (ZZm g Zh T T') ×ˢ Gam1 hs Zσ TT (ZZm g (Zh.map M.L.cj) T T')) ⊆ GR g Zh T T'

variable (hs : M.split = some g) {T T' : F} {TT : M.R}

theorem R_ext {x y : M.R} (h1 : p1 g x = p1 g y) (h2 : p2 g x = p2 g y) : x = y := Subtype.ext (g.e.injective (Prod.ext h1 h2))

theorem E_ext {x y : E} (h1 : p1 g x = p1 g y) (h2 : p2 g x = p2 g y) : x = y := g.e.injective (Prod.ext h1 h2)

theorem pdat_inj {k : E} {η₁ η₂ η₁' η₂' : M.R} {a₁ a₂ a₁' a₂' : E}
    (h : pdat g k η₁ a₁ η₁' a₁' = pdat g k η₂ a₂ η₂' a₂') : η₁ = η₂ ∧ a₁ = a₂ ∧ η₁' = η₂' ∧ a₁' = a₂' := by
  unfold pdat at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
  have e1 := congrArg g.e h1
  have e2 := congrArg g.e h2
  have e3 := congrArg g.e h3
  have e4 := congrArg g.e h4
  simp only [AlgEquiv.apply_symm_apply, Prod.mk.injEq] at e1 e2 e3 e4
  obtain ⟨a1, a2⟩ := e1
  obtain ⟨b1, b2⟩ := e2
  obtain ⟨c1, c2⟩ := e3
  obtain ⟨d1, d2⟩ := e4
  have hη : η₁ = η₂ := R_ext a1 d1
  have hη' : η₁' = η₂' := R_ext a2 d2
  subst hη hη'
  exact ⟨rfl, E_ext (sub_right_inj.mp c1) (sub_right_inj.mp b1), rfl,
    E_ext (sub_right_inj.mp c2) (sub_right_inj.mp b2)⟩

theorem asm_inj {Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E} {Z Zσ : M.Mat (r + 1)} (h : GHyp M g T T' TT Zh Z Zσ) :
    Function.Injective (asm hs h) := by
  rintro ⟨⟨x1, x2, x3, x4⟩, ⟨y1, y2, y3, y4⟩⟩ ⟨⟨x1', x2', x3', x4'⟩, ⟨y1', y2', y3', y4'⟩⟩ hab
  unfold asm at hab
  simp only [Prod.mk.injEq] at hab
  obtain ⟨h1, h2, h3⟩ := hab
  have e1 := (splitH hs h).symm.injective h1
  have e2 := (splitH hs h).symm.injective h2
  simp only [Prod.mk.injEq] at e1 e2
  obtain ⟨q1, q2, q3, q4⟩ := pdat_inj h3
  obtain ⟨e11, e12⟩ := e1
  obtain ⟨e21, e22⟩ := e2
  subst_vars
  rfl

def mapD {A B : Type} (θ : A → B) (p : A × A × M.R × E) : B × B × M.R × E := (θ p.1, θ p.2.1, p.2.2.1, p.2.2.2)

theorem asm_compat {Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E} {Z₁ Z₂ Zσ₁ Zσ₂ : M.Mat (r + 1)}
    (h₁ : GHyp M g T T' TT Zh₁ Z₁ Zσ₁) (h₂ : GHyp M g T T' TT Zh₂ Z₂ Zσ₂) (hk : KapEq Zh₁ Zh₂)
    (θ₁ : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT) (θ₂ : DD1 hs Zσ₁ TT ≃+ DD1 hs Zσ₂ TT)
    (ab : (DD1 hs Z₁ TT × DD1 hs Z₁ TT × M.R × E) × (DD1 hs Zσ₁ TT × DD1 hs Zσ₁ TT × M.R × E)) :
    (fun p => (thetaOf hs h₁ h₂ θ₁ θ₂ p.1, thetaOf hs h₁ h₂ θ₁ θ₂ p.2.1, p.2.2.1, p.2.2.2)) (asm hs h₁ ab) =
      asm hs h₂ (Prod.map (mapD (M := M) θ₁) (mapD (M := M) θ₂) ab) := by
  have hk' := kap_common hk h₁.2.2.2.2.2.1 h₂.2.2.2.2.2.1
  simp only [asm, thetaOf, AddEquiv.trans_apply, AddEquiv.apply_symm_apply, Prod.map, mapD, hk']
  rfl

end Formalism.L2.SG.LocalCountModules.AlgGSplit
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.AsmCompat =====

-- ===== clump member: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.GammaOneNonempty =====
-- clump-header: {"m": "Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.GammaOneNonempty", "h": "module\n\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.AsmCompat\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumA\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

namespace Formalism.L2.SG.LocalCountModules.AlgGSplit

theorem gammaOne_nonempty {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    {M : Model F E} {g : SplitG M.L} {r : ℕ} (hs : M.split = some g) (Z : M.Mat (r + 1)) (TT : M.R)
    (Zm : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : (Gam1 hs Z TT Zm).Nonempty :=
  ⟨_, 0, 0, rfl⟩

theorem gamSplit_of (hsub : GamSubP) (hsup : GamSupP) : GamSplitP := by
  intro F _ _ _ E _ _ _ _ M g hs r T T' TT Zh₁ Zh₂ Z₁ Z₂ Zσ₁ Zσ₂ h₁ h₂ hk θ₁ θ₂ _ _
  have e₁ : GR g Zh₁ T T' = asm hs h₁ '' (Gam1 hs Z₁ TT (ZZm g Zh₁ T T') ×ˢ
      Gam1 hs Zσ₁ TT (ZZm g (Zh₁.map M.L.cj) T T')) :=
    Set.Subset.antisymm (hsub F E M g hs r T T' TT Zh₁ Z₁ Zσ₁ h₁)
      (hsup F E M g hs r T T' TT Zh₁ Z₁ Zσ₁ h₁)
  have e₂ : GR g Zh₂ T T' = asm hs h₂ '' (Gam1 hs Z₂ TT (ZZm g Zh₂ T T') ×ˢ
      Gam1 hs Zσ₂ TT (ZZm g (Zh₂.map M.L.cj) T T')) :=
    Set.Subset.antisymm (hsub F E M g hs r T T' TT Zh₂ Z₂ Zσ₂ h₂)
      (hsup F E M g hs r T T' TT Zh₂ Z₂ Zσ₂ h₂)
  change _ '' GR g Zh₁ T T' = GR g Zh₂ T T' ↔ _
  rw [e₁, e₂, Set.image_image]
  simp_rw [asm_compat hs h₁ h₂ hk θ₁ θ₂]
  rw [← Set.image_image (asm hs h₂) (Prod.map (mapD θ₁) (mapD θ₂)),
    (Set.image_injective.mpr (asm_inj hs h₂)).eq_iff]
  have hp : (fun p => (mapD (M := M) θ₁ p.1, mapD (M := M) θ₂ p.2)) = Prod.map (mapD (M := M) θ₁) (mapD (M := M) θ₂) := rfl
  rw [← hp, ← Set.prod_image_image_eq, Set.prod_eq_prod_iff_of_nonempty]
  · rfl
  · exact (((gammaOne_nonempty hs _ _ _).image _).prod ((gammaOne_nonempty hs _ _ _).image _))

end Formalism.L2.SG.LocalCountModules.AlgGSplit
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.GammaOneNonempty =====

-- ===== clump member: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.SecondIsoComponentLinearOf =====
-- clump-header: {"m": "Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.SecondIsoComponentLinearOf", "h": "module\n\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.SecondCoeffSecondIdempotent\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumA\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

namespace Formalism.L2.SG.LocalCountModules.AlgGSplit

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ} (hs : M.split = some g)
variable {T T' : F} {TT : M.R} {Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
  {Z₁ Z₂ Zσ₁ Zσ₂ : M.Mat (r + 1)}
variable (h₁ : GHyp M g T T' TT Zh₁ Z₁ Zσ₁) (h₂ : GHyp M g T T' TT Zh₂ Z₂ Zσ₂)

theorem linear_firstIsoComponent (θ : DG g Zh₁ T T' ≃ₗ[M.L.O] DG g Zh₂ T T') : OLin hs (th1 hs h₁ h₂ θ) := by
  intro c l l₂ hl
  have key : ∀ x, th1 hs h₁ h₂ θ x = (splitH hs h₂ (θ ((splitH hs h₁).symm (x, 0)))).1 := fun x => rfl
  set v := (splitH hs h₁).symm (mk1 hs Z₁ TT l, 0) with hv
  have hv1 : splitH hs h₁ v = ((l : DD1 hs Z₁ TT), ((0 : Fin (r + 1) → M.R) : DD1 hs Zσ₁ TT)) := by
    rw [hv, AddEquiv.apply_symm_apply]
    rfl
  have hav := splitH_smul hs h₁ (dgO g c) v l 0 hv1
  rw [firstCoeff_diagonal, secondCoeff_diagonal, smul_zero] at hav
  have hθv : splitH hs h₂ (θ v) = ((l₂ : DD1 hs Z₂ TT), ((0 : Fin (r + 1) → M.R) : DD1 hs Zσ₂ TT)) := by
    refine Prod.ext ?_ ?_
    · rw [← key]
      exact hl
    · rw [lin_split1 hs h₁ h₂ θ (mk1 hs Z₁ TT l)]
      rfl
  have h2 := splitH_smul hs h₂ (dgO g c) (θ v) l₂ 0 hθv
  rw [firstCoeff_diagonal, secondCoeff_diagonal, smul_zero] at h2
  have hs1 : (splitH hs h₁).symm (mk1 hs Z₁ TT (dgR hs c • l), 0) = dgO g c • v := by
    rw [AddEquiv.symm_apply_eq, hav]
    rfl
  rw [key, hs1, LinearEquiv.map_smul, h2]

theorem linear_secondIsoComponent (θ : DG g Zh₁ T T' ≃ₗ[M.L.O] DG g Zh₂ T T') : OLin hs (th2 hs h₁ h₂ θ) := by
  intro c l l₂ hl
  have key : ∀ y, th2 hs h₁ h₂ θ y = (splitH hs h₂ (θ ((splitH hs h₁).symm (0, y)))).2 := fun y => rfl
  set v := (splitH hs h₁).symm (0, mk1 hs Zσ₁ TT l) with hv
  have hv1 : splitH hs h₁ v = (((0 : Fin (r + 1) → M.R) : DD1 hs Z₁ TT), (l : DD1 hs Zσ₁ TT)) := by
    rw [hv, AddEquiv.apply_symm_apply]
    rfl
  have hav := splitH_smul hs h₁ (dgO g c) v 0 l hv1
  rw [firstCoeff_diagonal, secondCoeff_diagonal, smul_zero] at hav
  have hθv : splitH hs h₂ (θ v) = (((0 : Fin (r + 1) → M.R) : DD1 hs Z₂ TT), (l₂ : DD1 hs Zσ₂ TT)) := by
    refine Prod.ext ?_ ?_
    · rw [lin_split2 hs h₁ h₂ θ (mk1 hs Zσ₁ TT l)]
      rfl
    · rw [← key]
      exact hl
  have h2 := splitH_smul hs h₂ (dgO g c) (θ v) 0 l₂ hθv
  rw [firstCoeff_diagonal, secondCoeff_diagonal, smul_zero] at h2
  have hs1 : (splitH hs h₁).symm (0, mk1 hs Zσ₁ TT (dgR hs c • l)) = dgO g c • v := by
    rw [AddEquiv.symm_apply_eq, hav]
    rfl
  rw [key, hs1, LinearEquiv.map_smul, h2]

theorem thetaOf_smul (θ₁ : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT) (θ₂ : DD1 hs Zσ₁ TT ≃+ DD1 hs Zσ₂ TT)
    (o₁ : OLin hs θ₁) (o₂ : OLin hs θ₂) (a : M.L.O) (v : DG g Zh₁ T T') :
    thetaOf hs h₁ h₂ θ₁ θ₂ (a • v) = a • thetaOf hs h₁ h₂ θ₁ θ₂ v := by
  obtain ⟨l, w, hlw⟩ := splitH_split hs h₁ v
  obtain ⟨l₂, hl₂⟩ := QuotientAddGroup.mk_surjective (θ₁ (l : DD1 hs Z₁ TT))
  obtain ⟨w₂, hw₂⟩ := QuotientAddGroup.mk_surjective (θ₂ (w : DD1 hs Zσ₁ TT))
  have e1 := o₁ (c1 g a) l l₂ hl₂.symm
  have e2 := o₂ (c2 g a) w w₂ hw₂.symm
  have hu : splitH hs h₂ (thetaOf hs h₁ h₂ θ₁ θ₂ v) = ((l₂ : DD1 hs Z₂ TT), (w₂ : DD1 hs Zσ₂ TT)) := by
    simp only [thetaOf, AddEquiv.trans_apply, AddEquiv.apply_symm_apply, hlw]
    exact Prod.ext hl₂.symm hw₂.symm
  have hau := splitH_smul hs h₂ a _ l₂ w₂ hu
  apply (splitH hs h₂).injective
  rw [hau]
  simp only [thetaOf, AddEquiv.trans_apply, AddEquiv.apply_symm_apply, splitH_smul hs h₁ a v l w hlw]
  exact Prod.ext e1 e2

def linOf (θ₁ : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT) (θ₂ : DD1 hs Zσ₁ TT ≃+ DD1 hs Zσ₂ TT)
    (o₁ : OLin hs θ₁) (o₂ : OLin hs θ₂) : DG g Zh₁ T T' ≃ₗ[M.L.O] DG g Zh₂ T T' where
  toFun := thetaOf hs h₁ h₂ θ₁ θ₂
  invFun := (thetaOf hs h₁ h₂ θ₁ θ₂).symm
  map_add' := map_add _
  map_smul' a v := thetaOf_smul hs h₁ h₂ θ₁ θ₂ o₁ o₂ a v
  left_inv := (thetaOf hs h₁ h₂ θ₁ θ₂).symm_apply_apply
  right_inv := (thetaOf hs h₁ h₂ θ₁ θ₂).apply_symm_apply

theorem firstIsoComponent_linearOf (θ₁ : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT) (θ₂ : DD1 hs Zσ₁ TT ≃+ DD1 hs Zσ₂ TT)
    (o₁ : OLin hs θ₁) (o₂ : OLin hs θ₂) : th1 hs h₁ h₂ (linOf hs h₁ h₂ θ₁ θ₂ o₁ o₂) = θ₁ := by
  ext x
  show (splitH hs h₂ (thetaOf hs h₁ h₂ θ₁ θ₂ ((splitH hs h₁).symm (x, 0)))).1 = θ₁ x
  simp only [thetaOf, AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
  rfl

theorem secondIsoComponent_linearOf (θ₁ : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT) (θ₂ : DD1 hs Zσ₁ TT ≃+ DD1 hs Zσ₂ TT)
    (o₁ : OLin hs θ₁) (o₂ : OLin hs θ₂) : th2 hs h₁ h₂ (linOf hs h₁ h₂ θ₁ θ₂ o₁ o₂) = θ₂ := by
  ext x
  show (splitH hs h₂ (thetaOf hs h₁ h₂ θ₁ θ₂ ((splitH hs h₁).symm (0, x)))).2 = θ₂ x
  simp only [thetaOf, AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
  rfl

theorem stepSplit_of (hG : GamSplitP) (hF : FormSplitP) : StepSplit := by
  intro F _ _ _ E _ _ _ _ M g hs r T T' TT Zh₁ Zh₂ Z₁ Z₂ Zσ₁ Zσ₂ h₁ h₂ hK
  have cond : ∀ (θ₁ : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT) (θ₂ : DD1 hs Zσ₁ TT ≃+ DD1 hs Zσ₂ TT)
      (o₁ : OLin hs θ₁) (o₂ : OLin hs θ₂),
      linOf hs h₁ h₂ θ₁ θ₂ o₁ o₂ ∈ ThetaGC M.L.O (↑M.L.cj) ((algebraMap F E) ↑g.q)
          ((algebraMap F E) (↑g.q)⁻¹) Zh₁ Zh₂ ((algebraMap F E) T) ((algebraMap F E) T') ↔
        Match1 hs θ₁ (ZZm g Zh₁ T T') (ZZm g Zh₂ T T') ∧
          Match1 hs θ₂ (ZZm g (Zh₁.map ⇑M.L.cj) T T') (ZZm g (Zh₂.map ⇑M.L.cj) T T') ∧
            IsoB hs Zh₁ Zh₂ T T' θ₁ θ₂ := by
    intro θ₁ θ₂ o₁ o₂
    have e := and_congr (hF F E M g hs r T T' TT Zh₁ Zh₂ Z₁ Z₂ Zσ₁ Zσ₂ h₁ h₂ θ₁ θ₂)
      (hG F E M g hs r T T' TT Zh₁ Zh₂ Z₁ Z₂ Zσ₁ Zσ₂ h₁ h₂ hK θ₁ θ₂ o₁ o₂)
    exact e.trans ⟨fun ⟨a, b, c⟩ => ⟨b, c, a⟩, fun ⟨b, c, a⟩ => ⟨a, b, c⟩⟩
  have back : ∀ θ : DG g Zh₁ T T' ≃ₗ[M.L.O] DG g Zh₂ T T',
      linOf hs h₁ h₂ (th1 hs h₁ h₂ θ) (th2 hs h₁ h₂ θ) (linear_firstIsoComponent hs h₁ h₂ θ) (linear_secondIsoComponent hs h₁ h₂ θ) = θ :=
    fun θ => LinearEquiv.ext fun v => (theta_eq hs h₁ h₂ θ v).symm
  refine Nat.card_congr
    { toFun := fun θ => ⟨(th1 hs h₁ h₂ θ.1, th2 hs h₁ h₂ θ.1), linear_firstIsoComponent hs h₁ h₂ θ.1,
        linear_secondIsoComponent hs h₁ h₂ θ.1, (cond _ _ (linear_firstIsoComponent hs h₁ h₂ θ.1) (linear_secondIsoComponent hs h₁ h₂ θ.1)).1
          ((back θ.1).symm ▸ θ.2)⟩
      invFun := fun p => ⟨linOf hs h₁ h₂ p.1.1 p.1.2 p.2.1 p.2.2.1,
        (cond _ _ p.2.1 p.2.2.1).2 p.2.2.2⟩
      left_inv := fun θ => Subtype.ext (back θ.1)
      right_inv := fun p => Subtype.ext (Prod.ext (firstIsoComponent_linearOf hs h₁ h₂ p.1.1 p.1.2 p.2.1 p.2.2.1)
        (secondIsoComponent_linearOf hs h₁ h₂ p.1.1 p.1.2 p.2.1 p.2.2.1)) }

end Formalism.L2.SG.LocalCountModules.AlgGSplit
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.SecondIsoComponentLinearOf =====

-- ===== clump member: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.SecondProjUniformizerMul =====
-- clump-header: {"m": "Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.SecondProjUniformizerMul", "h": "module\n\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.AsmCompat\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.SecondCoeffSecondIdempotent\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumA\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

namespace Formalism.L2.SG.LocalCountModules.AlgGSplit

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ} (hs : M.split = some g)

theorem firstProj_firstComponent (Y : Ix r → M.L.O) (b : Fin (r + 1)) : p1 g (cmp1 hs Y b : E) = p1 g (Y (Sum.inl b)) := by
  simp [p1, cmp1, e_rOf, c1]
theorem secondProj_firstComponent (Y : Ix r → M.L.O) (b : Fin (r + 1)) :
    p2 g (cmp1 hs Y b : E) = p1 g (Y (Sum.inl b)) + (g.q : F) * p1 g (Y (Sum.inr b)) := by
  simp [p1, p2, cmp1, e_rOf, c1]
theorem firstProj_secondComponent (Y : Ix r → M.L.O) (b : Fin (r + 1)) : p1 g (cmp2 hs Y b : E) = p2 g (Y (Sum.inl b)) := by
  simp [p1, p2, cmp2, e_rOf, c2]
theorem secondProj_secondComponent (Y : Ix r → M.L.O) (b : Fin (r + 1)) :
    p2 g (cmp2 hs Y b : E) = p2 g (Y (Sum.inl b)) + (g.q : F) * p2 g (Y (Sum.inr b)) := by
  simp [p2, cmp2, e_rOf, c2]
theorem firstProj_uniformizer_mul (x : M.R) : p1 g ((q2 hs * x : M.R) : E) = 0 := by
  simp [p1, q2]
theorem secondProj_uniformizer_mul (x : M.R) : p2 g ((q2 hs * x : M.R) : E) = (g.q : F) * p2 g (x : E) := by
  simp [p2, q2]

theorem dl_cast (a : Fin r) : dl (F := F) r a.castSucc = 0 := by
  unfold dl
  rw [ite_eq_right (Fin.castSucc_lt_last a).ne]

theorem gamSup_holds : GamSupP := by
  intro F _ _ _ E _ _ _ _ M g hs r T T' TT Zh Z Zσ h
  rintro _ ⟨⟨a, b⟩, ⟨⟨l, η, rfl⟩, ⟨l', η', rfl⟩⟩, rfl⟩
  have hZh : IsUnit Zh.det := h.2.2.2.2.2.1
  set u : Fin (r + 1) → M.R := η • (eV r : Fin (r + 1) → M.R) + q2 hs • l
  set u' : Fin (r + 1) → M.R := η' • (eV r : Fin (r + 1) → M.R) + q2 hs • l'
  set Y : Ix r → M.L.O := iota1 hs u + iota2 hs u'
  set Y'' : Ix r → M.L.O := iota1 hs l + iota2 hs l'
  set Y' : Ix r → M.L.O := Y - dgO g g.q • Y''
  have h1 : cmp1 hs Y = u := by simp only [Y, map_add (f := _), firstComponent_iotaOne, firstComponent_iotaTwo, add_zero]
  have h2 : cmp2 hs Y = u' := by simp only [Y, map_add (f := _), secondComponent_iotaOne, secondComponent_iotaTwo, zero_add]
  have h3 : cmp1 hs Y'' = l := by simp only [Y'', map_add (f := _), firstComponent_iotaOne, firstComponent_iotaTwo, add_zero]
  have h4 : cmp2 hs Y'' = l' := by simp only [Y'', map_add (f := _), secondComponent_iotaOne, secondComponent_iotaTwo, zero_add]
  have hY : ∀ i, (Y i : E) - Y' i = algebraMap F E (g.q : F) * Y'' i := fun i => by
    simp only [Y', Pi.sub_apply, Pi.smul_apply, smul_eq_mul, dgO, AddSubgroupClass.coe_sub,
      MulMemClass.coe_mul]
    ring
  have hW1 : ∀ i, p1 g (Y' i) = p1 g (Y i) - (g.q : F) * p1 g (Y'' i) := fun i => by
    have := congrArg (p1 g) (hY i); rw [map_sub, map_mul, firstProj_algebraMap_split] at this; linear_combination -this
  have hW2 : ∀ i, p2 g (Y' i) = p2 g (Y i) - (g.q : F) * p2 g (Y'' i) := fun i => by
    have := congrArg (p2 g) (hY i); rw [map_sub, map_mul, secondProj_algebraMap_split] at this; linear_combination -this
  have fY := components_of_firstComponent_eq hs h1
  have gY := components_of_secondComponent_eq hs h2
  have fZ := components_of_firstComponent_eq hs h3
  have gZ := components_of_secondComponent_eq hs h4
  simp only [u, u', firstProj_unit_vector_eq hs, secondProj_unit_vector_eq hs] at fY gY
  refine ⟨Y, Y', Y'', fun a => ?_, fun a => ?_, hY, ?_⟩
  · apply Subtype.ext
    apply E_ext (g := g)
    · rw [(fY _).1, dl_cast, mul_zero, ZeroMemClass.coe_zero, map_zero]
    · rw [(gY _).1, dl_cast, mul_zero, ZeroMemClass.coe_zero, map_zero]
  · apply E_ext (g := g)
    · rw [map_add (f := _), map_mul, firstProj_algebraMap_split, hW1, hW1, map_zero]
      linear_combination (fY a.castSucc).2 - (g.q : F) * (fZ a.castSucc).2 + p2 g η * dl_cast (F := F) a
    · rw [map_add (f := _), map_mul, secondProj_algebraMap_split, hW2, hW2, map_zero]
      linear_combination (gY a.castSucc).2 - (g.q : F) * (gZ a.castSucc).2 + p2 g η' * dl_cast (F := F) a
  · exact Prod.ext rfl (Prod.ext rfl (vals hs hZh T T' h1 h2 h3 h4 hY).symm)

theorem gamSub_holds : GamSubP := by
  intro F _ _ _ E _ _ _ _ M g hs r T T' TT Zh Z Zσ h
  rintro _ ⟨Y, Y', Y'', c1, c2, c3, rfl⟩
  have hZh : IsUnit Zh.det := h.2.2.2.2.2.1
  set l := cmp1 hs Y''
  set l' := cmp2 hs Y''
  set η : M.R := cmp1 hs Y (Fin.last r) - q2 hs * l (Fin.last r)
  set η' : M.R := cmp2 hs Y (Fin.last r) - q2 hs * l' (Fin.last r)
  have hW1 : ∀ i, p1 g (Y' i) = p1 g (Y i) - (g.q : F) * p1 g (Y'' i) := fun i => by
    have := congrArg (p1 g) (c3 i); rw [map_sub, map_mul, firstProj_algebraMap_split] at this; linear_combination -this
  have hW2 : ∀ i, p2 g (Y' i) = p2 g (Y i) - (g.q : F) * p2 g (Y'' i) := fun i => by
    have := congrArg (p2 g) (c3 i); rw [map_sub, map_mul, secondProj_algebraMap_split] at this; linear_combination -this
  have h1 : cmp1 hs Y = η • (eV r : Fin (r + 1) → M.R) + q2 hs • l := by
    funext b
    apply R_ext (g := g)
    · rw [firstProj_unit_vector_eq hs, firstProj_firstComponent]
      by_cases hb : b = Fin.last r
      · subst hb
        simp only [η, AddSubgroupClass.coe_sub, map_sub, firstProj_uniformizer_mul, firstProj_firstComponent, dl_last, mul_one, sub_zero]
      · obtain ⟨a, rfl⟩ := Fin.exists_castSucc_eq.2 hb
        rw [c1 a, dl_cast, mul_zero, ZeroMemClass.coe_zero, map_zero]
    · rw [secondProj_unit_vector_eq hs, secondProj_firstComponent]
      by_cases hb : b = Fin.last r
      · subst hb
        simp only [η, l, AddSubgroupClass.coe_sub, map_sub, secondProj_uniformizer_mul, secondProj_firstComponent, dl_last, mul_one]
        ring
      · obtain ⟨a, rfl⟩ := Fin.exists_castSucc_eq.2 hb
        have e := congrArg (p1 g) (c2 a)
        rw [map_add (f := _), map_mul, firstProj_algebraMap_split, hW1, hW1, map_zero] at e
        simp only [l, secondProj_firstComponent, dl_cast, mul_zero, zero_add]
        linear_combination e
  have h2 : cmp2 hs Y = η' • (eV r : Fin (r + 1) → M.R) + q2 hs • l' := by
    funext b
    apply R_ext (g := g)
    · rw [firstProj_unit_vector_eq hs, firstProj_secondComponent]
      by_cases hb : b = Fin.last r
      · subst hb
        simp only [η', AddSubgroupClass.coe_sub, map_sub, firstProj_uniformizer_mul, firstProj_secondComponent, dl_last, mul_one, sub_zero]
      · obtain ⟨a, rfl⟩ := Fin.exists_castSucc_eq.2 hb
        have e := congrArg Prod.snd (congrArg g.e (congrArg Subtype.val (c1 a)))
        rw [dl_cast, mul_zero]
        simpa [adele_ext_components] using e
    · rw [secondProj_unit_vector_eq hs, secondProj_secondComponent]
      by_cases hb : b = Fin.last r
      · subst hb
        simp only [η', l', AddSubgroupClass.coe_sub, map_sub, secondProj_uniformizer_mul, secondProj_secondComponent, dl_last, mul_one]
        ring
      · obtain ⟨a, rfl⟩ := Fin.exists_castSucc_eq.2 hb
        have e := congrArg (p2 g) (c2 a)
        rw [map_add (f := _), map_mul, secondProj_algebraMap_split, hW2, hW2, map_zero] at e
        simp only [l', secondProj_secondComponent, dl_cast, mul_zero, zero_add]
        linear_combination e
  refine ⟨(((QuotientAddGroup.mk (cmp1 hs Y) : DD1 hs Z TT), (QuotientAddGroup.mk l : DD1 hs Z TT), η,
      laG (ZZm g Zh T T') l), ((QuotientAddGroup.mk (cmp2 hs Y) : DD1 hs Zσ TT),
      (QuotientAddGroup.mk l' : DD1 hs Zσ TT), η', laG (ZZm g (Zh.map M.L.cj) T T') l')),
    ⟨⟨l, η, by rw [h1]⟩, ⟨l', η', by rw [h2]⟩⟩, ?_⟩
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · exact (splitH hs h).symm_apply_apply (Submodule.Quotient.mk Y)
  · exact (splitH hs h).symm_apply_apply (Submodule.Quotient.mk Y'')
  · exact (vals hs hZh T T' h1 h2 rfl rfl c3).symm

end Formalism.L2.SG.LocalCountModules.AlgGSplit
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.SecondProjUniformizerMul =====

-- ===== clump member: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.FormSplit =====
-- clump-header: {"m": "Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.FormSplit", "h": "module\n\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.FormSplitP\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.ZzMinusSecondProjTranspose\nimport Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.SharpEquivApply\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.SecondProjConjApply\nimport Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.SecondProjConjEqFirstProj\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\nimport Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumA\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

namespace Formalism.L2.SG.LocalCountModules.AlgGSplit

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

section FormSplit

theorem fs_add_left (O : Subring E) (cj : E →+* E) (qi : E) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (T T' : E) (Y Y' W : Ix r → O) :
    formG O cj qi Z T T' (Y + Y') W = formG O cj qi Z T T' Y W + formG O cj qi Z T T' Y' W := by
  unfold formG
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply, Subring.coe_add]
  ring

theorem fs_add_right (O : Subring E) (cj : E →+* E) (qi : E) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (T T' : E) (Y W W' : Ix r → O) :
    formG O cj qi Z T T' Y (W + W') = formG O cj qi Z T T' Y W + formG O cj qi Z T T' Y W' := by
  unfold formG
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply, Subring.coe_add, map_add (f := _)]
  ring

theorem splitSecondProj_iotaOne (hs : M.split = some g) (l : Fin (r + 1) → M.R) (i : Ix r) :
    ph2 g ((iota1 hs l i : M.L.O) : E) = 0 := by
  rcases i with a | a
  · rw [secondProj_apply, e_iota1_inl]
  · rw [secondProj_apply, e_iota1_inr]

theorem splitFirstProj_iotaTwo (hs : M.split = some g) (l : Fin (r + 1) → M.R) (i : Ix r) :
    ph1 g ((iota2 hs l i : M.L.O) : E) = 0 := by
  rw [firstProj_apply, e_iota2]

theorem splitForm_iotaOne_iotaOne (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (l w : Fin (r + 1) → M.R) :
    formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T) (algebraMap F E T')
      (iota1 hs l) (iota1 hs w) = 0 := by
  rw [eq_iff_ph (g := g)]
  unfold formG

  simp only [map_sum, map_mul, map_zero, firstProj_conj_eq_secondProj, _root_.Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork.secondProj_conj_eq_firstProj, splitSecondProj_iotaOne, mul_zero, zero_mul,
  Finset.sum_const_zero]
  simp

theorem splitForm_iotaTwo_iotaTwo (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (l w : Fin (r + 1) → M.R) :
    formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T) (algebraMap F E T')
      (iota2 hs l) (iota2 hs w) = 0 := by
  rw [eq_iff_ph (g := g)]
  unfold formG

  simp only [map_sum, map_mul, map_zero, firstProj_conj_eq_secondProj, _root_.Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork.secondProj_conj_eq_firstProj, splitFirstProj_iotaTwo, mul_zero, zero_mul,
  Finset.sum_const_zero]
  simp

theorem fs_map_inv {n : Type} [Fintype n] [DecidableEq n] (f : E →+* E) (A : Matrix n n E) (hA : IsUnit A.det) :
    (A⁻¹).map f = (A.map f)⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hA, Matrix.map_one _ (map_zero f) (map_one f)]

theorem fs_gram_herm (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' q : F) (i j : Ix r) :
    (M.L.cj : E →+* E) (gramG (M.L.cj : E →+* E) (algebraMap F E q) Zh (algebraMap F E T) (algebraMap F E T') j i) =
      gramG (M.L.cj : E →+* E) (algebraMap F E q) Zh (algebraMap F E T) (algebraMap F E T') i j := by
  rcases i with a | a <;> rcases j with b | b <;> by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r <;>
    simp [gramG, cor, ha, hb, map_mul, map_add (f := _), map_neg, map_sub, M.L.cj_cj, AlgEquiv.commutes] <;> ring

theorem fs_herm (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' q : F)
    (hU : IsUnit (gramG (M.L.cj : E →+* E) (algebraMap F E q) Zh (algebraMap F E T) (algebraMap F E T')).det)
    (Y W : Ix r → M.L.O) :
    formG M.L.O (M.L.cj : E →+* E) (algebraMap F E q) Zh (algebraMap F E T) (algebraMap F E T') Y W =
      (M.L.cj : E →+* E)
        (formG M.L.O (M.L.cj : E →+* E) (algebraMap F E q) Zh (algebraMap F E T) (algebraMap F E T') W Y) := by
  obtain ⟨G, hGd⟩ : ∃ G, gramG (M.L.cj : E →+* E) (algebraMap F E q) Zh (algebraMap F E T) (algebraMap F E T') = G :=
    ⟨_, rfl⟩
  rw [hGd] at hU
  have hT : G.map (M.L.cj : E →+* E) = G.transpose := by
    ext i j; rw [Matrix.map_apply, Matrix.transpose_apply, ← hGd, fs_gram_herm]
  have hinv : ∀ i j, (M.L.cj : E →+* E) (G⁻¹ i j) = G⁻¹ j i := by
    intro i j
    have := congrFun (congrFun (fs_map_inv (M.L.cj : E →+* E) G hU) i) j
    rw [Matrix.map_apply] at this
    have h2 : (G.transpose)⁻¹ = (G⁻¹).transpose := by rw [Matrix.transpose_nonsing_inv]
    rw [this, hT, h2, Matrix.transpose_apply]
  have hcc : ∀ x : E, (M.L.cj : E →+* E) ((M.L.cj : E →+* E) x) = x := M.L.cj_cj
  unfold formG

  simp only [hGd, map_sum, map_mul, hcc, hinv]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem fs_split (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (hU : IsUnit (gramG (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T)
      (algebraMap F E T')).det)
    (Y W : Ix r → M.L.O) :
    formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T) (algebraMap F E T') Y W =
      formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T) (algebraMap F E T')
          (iota1 hs (cmp1 hs Y)) (iota2 hs (cmp2 hs W)) +
        (M.L.cj : E →+* E) (formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T)
          (algebraMap F E T') (iota1 hs (cmp1 hs W)) (iota2 hs (cmp2 hs Y))) := by
  conv_lhs => rw [← iota_cmp hs Y, ← iota_cmp hs W]
  rw [fs_add_left, fs_add_right, fs_add_right, splitForm_iotaOne_iotaOne, splitForm_iotaTwo_iotaTwo,
    fs_herm Zh T T' _ hU (iota2 hs (cmp2 hs Y)) (iota1 hs (cmp1 hs W))]
  ring

theorem fs_rel (hs : M.split = some g) {T T' : F} {TT : M.R} {Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    {Z₁ Z₂ Zσ₁ Zσ₂ : M.Mat (r + 1)} (h₁ : GHyp M g T T' TT Zh₁ Z₁ Zσ₁) (h₂ : GHyp M g T T' TT Zh₂ Z₂ Zσ₂)
    (θ₁ : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT) (θ₂ : DD1 hs Zσ₁ TT ≃+ DD1 hs Zσ₂ TT) (Y Y₂ : Ix r → M.L.O) :
    thetaOf hs h₁ h₂ θ₁ θ₂ (Submodule.Quotient.mk Y) = Submodule.Quotient.mk Y₂ ↔
      θ₁ (QuotientAddGroup.mk (cmp1 hs Y)) = QuotientAddGroup.mk (cmp1 hs Y₂) ∧
        θ₂ (QuotientAddGroup.mk (cmp2 hs Y)) = QuotientAddGroup.mk (cmp2 hs Y₂) := by
  rw [thetaOf, AddEquiv.trans_apply, AddEquiv.trans_apply, AddEquiv.symm_apply_eq]
  simp [splitH, splitQ_mk, Prod.ext_iff]
  exact Iff.rfl

theorem formSplit_holds : FormSplitP := by
  intro F _ _ _ E _ _ _ _ M g hs r T T' TT Zh₁ Zh₂ Z₁ Z₂ Zσ₁ Zσ₂ h₁ h₂ θ₁ θ₂
  have hU₁ := unitGramG_holds F E M g hs r T T' TT Zh₁ Z₁ Zσ₁ h₁
  have hU₂ := unitGramG_holds F E M g hs r T T' TT Zh₂ Z₂ Zσ₂ h₂
  constructor
  · intro hF l l₂ w w₂ hl hw
    refine hF (iota1 hs l) (iota2 hs w) (iota1 hs l₂) (iota2 hs w₂) ?_ ?_
    · rw [fs_rel, firstComponent_iotaOne, firstComponent_iotaOne, secondComponent_iotaOne, secondComponent_iotaOne]
      exact ⟨hl, by simp⟩
    · rw [fs_rel, firstComponent_iotaTwo, firstComponent_iotaTwo, secondComponent_iotaTwo, secondComponent_iotaTwo]
      exact ⟨by simp, hw⟩
  · intro hB Y W Y₂ W₂ hY hW
    rw [fs_rel] at hY hW
    rw [fs_split hs Zh₂ T T' hU₂, fs_split hs Zh₁ T T' hU₁]
    have e1 := hB (cmp1 hs Y) (cmp1 hs Y₂) (cmp2 hs W) (cmp2 hs W₂) hY.1 hW.2
    have e2 := hB (cmp1 hs W) (cmp1 hs W₂) (cmp2 hs Y) (cmp2 hs Y₂) hW.1 hY.2
    have e2' : (M.L.cj : E →+* E) (formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh₂
        (algebraMap F E T) (algebraMap F E T') (iota1 hs (cmp1 hs W₂)) (iota2 hs (cmp2 hs Y₂)) -
      formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh₁ (algebraMap F E T) (algebraMap F E T')
        (iota1 hs (cmp1 hs W)) (iota2 hs (cmp2 hs Y))) ∈ M.L.O := cj_mem_O M.L e2
    convert add_mem e1 e2' using 1
    rw [map_sub]
    ring

end FormSplit

end Formalism.L2.SG.LocalCountModules.AlgGSplit
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.FormSplit =====

-- ===== clump member: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.StepSplitHolds =====
-- clump-header: {"m": "Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.StepSplitHolds", "h": "module\n\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.FormSplitP\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.GammaOneNonempty\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.SecondIsoComponentLinearOf\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.SecondProjUniformizerMul\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.FormSplit\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace Formalism.L2.SG.LocalCountModules.AlgGSplit

theorem gamSplit_holds : GamSplitP := gamSplit_of gamSub_holds gamSup_holds

theorem stepSplit_holds : Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork.StepSplit := stepSplit_of gamSplit_holds formSplit_holds

end Formalism.L2.SG.LocalCountModules.AlgGSplit
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.StepSplitHolds =====
