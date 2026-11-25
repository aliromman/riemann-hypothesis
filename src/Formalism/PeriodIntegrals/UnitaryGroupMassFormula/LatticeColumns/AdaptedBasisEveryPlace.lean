module

public import Formalism.HermitianCurvature.MemParahoricTimesPrincipalCongruenceIff
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.HModelAllOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SecondCoordsCongruentMod
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.InGMulInt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.AdqHRRatV
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.PsiVIteOne
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.FirstCoordsMulVec
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.SecondProjWeightVectorZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ExistsGlOfLeftInv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.FrAIntReindex
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.MatRMulMatC
import Mathlib.Tactic.Linter.Style
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.CharZeroAdicCompletion
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SplitLatticeBasisExists
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.SumKfMulZREqZero

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.HAdaptGen, Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.HAdaptRed, Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.AdaptInDet, Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.DotPTPinv, Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.HacFrame, Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.AdaptedBasisEveryPlace

-- ===== clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.HAdaptGen =====
-- clump-header: {"m": "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.HAdaptGen", "h": "module\n\npublic import Formalism.HermitianCurvature.MemParahoricTimesPrincipalCongruenceIff\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace PIW.MassDataColumns

open Matrix Formalism.FourierDecayAlt.S3
open scoped Matrix

variable {K : Type} [Field K] (O : Subring K) {r k : ℕ}

def colv (c : Idx r k → Idx r k → K) (y : Fin k → Idx r k → K) : Idx r k → Idx r k → K
  | Sum.inr (Sum.inl (Sum.inl i)) => y i
  | Sum.inl a => c (Sum.inl a)
  | Sum.inr (Sum.inl (Sum.inr u)) => c (Sum.inr (Sum.inl (Sum.inr u)))
  | Sum.inr (Sum.inr b) => c (Sum.inr (Sum.inr b))

def ofCols (v : Idx r k → Idx r k → K) : Matrix (Idx r k) (Idx r k) K := fun i j => v j i

section Gen


def IntO (M : Matrix (Idx r k) (Idx r k) K) : Prop := ∀ i j, M i j ∈ O

end Gen

end PIW.MassDataColumns
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.HAdaptGen =====

-- ===== clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.HAdaptRed =====
-- clump-header: {"m": "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.HAdaptRed", "h": "module\n\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.HAdaptGen\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.HModelAllOf\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.PiTensorProduct\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain Formalism.FourierDecayAlt.S3 MassDataIdxSteps MassDataIdxStIm MassDataIdxSpl
open scoped Matrix TensorProduct

variable {D : D7}

section In

variable (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X)
  (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)

def cV (s : Idx D.R.rS D.R.k) : Idx D.R.rS D.R.k → FpX X p :=
  pr1 θ (ratV (F := X.B.I.F) (FpX X p) (vecAt (frameOf X u) s)) ∘ (idxEquiv X).symm

def aV (s : Idx D.R.rS D.R.k) : Idx D.R.rS D.R.k → FpX X p :=
  (Matrix.reindex (idxEquiv X) (idxEquiv X) (jm1 X.B.I.J θ))ᵀ *ᵥ
    (pr2 θ (ratV (F := X.B.I.F) (FpX X p) (vecAt (frameOf X u) s)) ∘ (idxEquiv X).symm)

def yV (i : Fin D.R.k) : Idx D.R.rS D.R.k → FpX X p :=
  pr1 θ (((HA.mat (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (PI.MassDataKppVolLemmas.piV X.B.I p.1 (finHA X hb (X.xu u))) :
      GL (Fin X.B.I.n) (TpX X p)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (TpX X p)) *ᵥ
      PI.FinKW.vecV X.B.I p.1 (X.bw i)) ∘ (idxEquiv X).symm

end In

def AdaptIn (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X) : Prop :=
  ∃ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ ∧
    ∃ P : GL (Idx D.R.rS D.R.k) (FpX X p), LatBasis X p θ (reindex₂ X p P) ∧
    ∃ (l : Idx D.R.rS D.R.k → FpX X p) (o : Idx D.R.rS D.R.k → Fin D.R.k → FpX X p) (uu : FpX X p),
      (∀ s t, ¬ IsW s → ¬ IsW t → aV X u p θ s ⬝ᵥ cV X u p θ t = if t = dlH s then l s else 0) ∧
      (∀ s i, ¬ IsW s → aV X u p θ s ⬝ᵥ yV X hb u p θ i = ((gOf p : ℕ) : FpX X p) * o s i) ∧
      (∀ s, ¬ IsW s → l s ≠ 0) ∧ (∀ s, ¬ IsW s → (l s)⁻¹ ∈ p.1.adicCompletionIntegers X.B.I.F) ∧
      (∀ s i, o s i ∈ p.1.adicCompletionIntegers X.B.I.F) ∧
      IntO (p.1.adicCompletionIntegers X.B.I.F).toSubring
        (((P⁻¹ : GL (Idx D.R.rS D.R.k) (FpX X p)) : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) *
          ofCols (colv (cV X u p θ) (yV X hb u p θ))) ∧
      uu ∈ p.1.adicCompletionIntegers X.B.I.F ∧
      (((P⁻¹ : GL (Idx D.R.rS D.R.k) (FpX X p)) : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) *
          ofCols (colv (cV X u p θ) (yV X hb u p θ))).det * uu = 1

private theorem mulVec_apply_eq_sum_lattice_columns {ι κ K : Type} [Fintype κ] [Field K] (M : Matrix ι κ K) (v : κ → K)
    (i : ι) : (M *ᵥ v) i = ∑ j, M i j * v j := rfl

private theorem dotProduct_eq_sum_mul {κ K : Type} [Fintype κ] [Field K] (v w : κ → K) :
    v ⬝ᵥ w = ∑ j, v j * w j := rfl

private theorem dotProduct_comm_field {κ K : Type} [Fintype κ] [Field K] (v w : κ → K) :
    v ⬝ᵥ w = w ⬝ᵥ v := by
  rw [dotProduct_eq_sum_mul, dotProduct_eq_sum_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

private theorem colv_apply_of_not_isW {r k : ℕ} {K : Type} [Field K] (c : Idx r k → Idx r k → K)
    (y : Fin k → Idx r k → K) (s : Idx r k) (hs : ¬ IsW s) : colv c y s = c s := by
  rcases s with a | ((i | u) | b)
  · rfl
  · exact absurd ⟨i, rfl⟩ hs
  · rfl
  · rfl

private theorem ofCols_mulVec_single_one {r k : ℕ} {K : Type} [Field K] (v : Idx r k → Idx r k → K)
    (s : Idx r k) : ofCols v *ᵥ Pi.single s 1 = v s := by
  funext i
  rw [mulVec_apply_eq_sum_lattice_columns]
  simp [ofCols, Pi.single_apply]

private theorem ofCols_transpose_mulVec_apply {r k : ℕ} {K : Type} [Field K] (v : Idx r k → Idx r k → K)
    (w : Idx r k → K) (t : Idx r k) : ((ofCols v)ᵀ *ᵥ w) t = v t ⬝ᵥ w := by
  first
  | rfl

private theorem ofCols_mulVec_eq_sum_smul {r k : ℕ} {K : Type} [Field K] (v : Idx r k → Idx r k → K)
    (w : Idx r k → K) : ofCols v *ᵥ w = ∑ j, w j • v j := by
  funext i
  rw [mulVec_apply_eq_sum_lattice_columns, Finset.sum_apply]
  simp [ofCols, mul_comm]

private theorem ofCols_colv_zero_mulVec_eq_zero_of_isW {r k : ℕ} {K : Type} [Field K] (z : Fin k → Idx r k → K)
    (w : Idx r k → K) (hw : ∀ j, IsW j → w j = 0) : ofCols (colv (fun _ => 0) z) *ᵥ w = 0 := by
  rw [ofCols_mulVec_eq_sum_smul]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : IsW j
  · rw [hw j hj, zero_smul]
  · simp [colv_apply_of_not_isW _ _ j hj]

private theorem ofCols_colv_zero_mul_self_eq_zero_of_isW {r k : ℕ} {K : Type} [Field K] (z : Fin k → Idx r k → K)
    (hz : ∀ i j, IsW j → z i j = 0) :
    ofCols (colv (fun _ => 0) z) * ofCols (colv (fun _ => 0) z) = 0 := by
  ext a b
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : IsW j
  · by_cases hb : IsW b
    · obtain ⟨i, rfl⟩ := hb
      simp [ofCols, colv, hz i j hj]
    · simp [ofCols, colv_apply_of_not_isW _ _ b hb]
  · simp [ofCols, colv_apply_of_not_isW _ _ j hj]

private theorem mulVec_apply_mem_of_mem {ι κ K : Type} [Fintype κ] [Field K] (S : ValuationSubring K)
    (M : Matrix ι κ K) (hM : ∀ i j, M i j ∈ S) (v : κ → K) (hv : ∀ j, v j ∈ S) (i : ι) :
    (M *ᵥ v) i ∈ S := by
  rw [mulVec_apply_eq_sum_lattice_columns]
  exact sum_mem fun j _ => mul_mem (hM i j) (hv j)

private theorem mulVec_mem_iff_of_mul_eq_one_of_mem {κ K : Type} [Fintype κ] [DecidableEq κ] [Field K] (S : ValuationSubring K)
    (N N' : Matrix κ κ K) (h : N * N' = 1) (hN : ∀ i j, N i j ∈ S) (hN' : ∀ i j, N' i j ∈ S)
    (w : κ → K) : (∀ i, (N' *ᵥ w) i ∈ S) ↔ ∀ i, w i ∈ S := by
  constructor
  · intro hw i
    have hw' : w = N *ᵥ (N' *ᵥ w) := by rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
    rw [hw']
    exact mulVec_apply_mem_of_mem S N hN _ hw i
  · intro hw i
    exact mulVec_apply_mem_of_mem S N' hN' w hw i

private theorem matrix_mul_apply_mem_of_mem {κ K : Type} [Fintype κ] [Field K] (S : ValuationSubring K)
    (M E : Matrix κ κ K) (hM : ∀ i j, M i j ∈ S) (hE : ∀ i j, E i j ∈ S) (i j : κ) :
    (M * E) i j ∈ S := by
  rw [Matrix.mul_apply]
  exact sum_mem fun l _ => mul_mem (hM i l) (hE l j)

private theorem adjugate_apply_mem_of_forall_mem {κ K : Type} [Fintype κ] [DecidableEq κ] [Field K] (S : ValuationSubring K)
    (M : Matrix κ κ K) (hM : ∀ i j, M i j ∈ S) (i j : κ) : M.adjugate i j ∈ S := by
  let M' : Matrix κ κ S.toSubring := fun a b => ⟨M a b, hM a b⟩
  have hMeq : M = (S.toSubring.subtype).mapMatrix M' := by
    ext a b
    rfl
  rw [hMeq, ← RingHom.map_adjugate]
  exact (M'.adjugate i j).2

private theorem latBasis_mul_of_mem_integers_of_inv_mem (X : HidaSetting D) (p : TypX X)
    (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) (P R : GL (Fin X.B.I.n) (FpX X p))
    (hR : ∀ i j, (R : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p)) i j ∈
      p.1.adicCompletionIntegers X.B.I.F)
    (hR' : ∀ i j, ((R⁻¹ : GL (Fin X.B.I.n) (FpX X p)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p)) i j ∈
      p.1.adicCompletionIntegers X.B.I.F)
    (h : LatBasis X p θ P) : LatBasis X p θ (P * R) := by
  unfold LatBasis at h ⊢
  intro x
  rw [h x]
  have e1 : (((P * R)⁻¹ : GL (Fin X.B.I.n) (FpX X p)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p)) =
      ((R⁻¹ : GL (Fin X.B.I.n) (FpX X p)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p)) *
        ((P⁻¹ : GL (Fin X.B.I.n) (FpX X p)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p)) := by
    rw [mul_inv_rev, Units.val_mul]
  have e2 : ((P * R : GL (Fin X.B.I.n) (FpX X p)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p))ᵀ =
      (R : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p))ᵀ *
        (P : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p))ᵀ := by
    rw [Units.val_mul, Matrix.transpose_mul]
  rw [e1, e2]
  simp only [← Matrix.mulVec_mulVec]
  refine and_congr ?_ ?_
  · refine (mulVec_mem_iff_of_mul_eq_one_of_mem _ (R : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p)) _ ?_ hR hR' _).symm
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  · refine (mulVec_mem_iff_of_mul_eq_one_of_mem _ ((R⁻¹ : GL (Fin X.B.I.n) (FpX X p)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p))ᵀ
      (R : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p))ᵀ ?_ (fun i j => hR' j i) (fun i j => hR j i) _).symm
    rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one]



theorem hAdaptQ_of_in (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X)
    (h : AdaptIn X hb u p) : HAdaptQ X hb u p := by
  classical
  obtain ⟨θ, hθ, P, hP, l, o, uu, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  let cc : Fin D.R.k → Idx D.R.rS D.R.k → FpX X p := fun i t =>
    if IsW t then 0 else -(o (dlH t) i) * (l (dlH t))⁻¹
  let z : Fin D.R.k → Idx D.R.rS D.R.k → FpX X p := fun i t => ((gOf p : ℕ) : FpX X p) * cc i t
  have hccW : ∀ i j, IsW j → cc i j = 0 := fun i j hj => by simp [cc, hj]
  have hz : ∀ i j, IsW j → z i j = 0 := fun i j hj => by simp [z, hccW i j hj]
  have hcc : ∀ i t, cc i t ∈ p.1.adicCompletionIntegers X.B.I.F := by
    intro i t
    by_cases ht : IsW t
    · rw [hccW i t ht]
      exact zero_mem _
    · simp only [cc, ite_eq_right ht]
      exact mul_mem (neg_mem (h5 _ _)) (h4 _ (_root_.PIW.MassDataColumns.dlH_frame t ht))
  have hgO : ((gOf p : ℕ) : FpX X p) ∈ p.1.adicCompletionIntegers X.B.I.F := natCast_mem _ _
  obtain ⟨A, hA⟩ : ∃ A : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p),
      A = ofCols (colv (cV X u p θ) (yV X hb u p θ)) := ⟨_, rfl⟩
  obtain ⟨Nn, hNn⟩ : ∃ Nn : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p),
      Nn = ofCols (colv (fun _ => 0) z) := ⟨_, rfl⟩
  rw [← hA] at h6 h8
  have hsq : Nn * Nn = 0 := by
    rw [hNn]
    exact ofCols_colv_zero_mul_self_eq_zero_of_isW z hz
  have hE1 : (1 + Nn) * (1 - Nn) = 1 := by
    first
    | simp [add_mul, mul_sub, hsq]
  have hE2 : (1 - Nn) * (1 + Nn) = 1 := by
    first
    | simp [sub_mul, mul_add, hsq]
  have hAdet : IsUnit A.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [Matrix.det_mul, h0, mul_zero, zero_mul] at h8
    exact zero_ne_one h8
  let Eu : GL (Idx D.R.rS D.R.k) (FpX X p) := ⟨1 + Nn, 1 - Nn, hE1, hE2⟩
  let Q : GL (Idx D.R.rS D.R.k) (FpX X p) := Matrix.nonsingInvUnit A hAdet * Eu
  have hQ : (Q : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) = A * (1 + Nn) := rfl
  have hAs : ∀ s, ¬ IsW s → A *ᵥ Pi.single s 1 = cV X u p θ s := fun s hs => by
    rw [hA, ofCols_mulVec_single_one, colv_apply_of_not_isW _ _ s hs]
  have hAw : ∀ i, A *ᵥ Pi.single (wI i) 1 = yV X hb u p θ i := fun i => by
    rw [hA, ofCols_mulVec_single_one]
    rfl
  have hNs : ∀ s, ¬ IsW s → Nn *ᵥ Pi.single s 1 = 0 := fun s hs => by
    rw [hNn, ofCols_mulVec_single_one, colv_apply_of_not_isW _ _ s hs]
  have hNw : ∀ i, Nn *ᵥ Pi.single (wI i) 1 = z i := fun i => by
    rw [hNn, ofCols_mulVec_single_one]
    rfl
  have hQs : ∀ s, ¬ IsW s →
      (Q : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) *ᵥ Pi.single s 1 = cV X u p θ s :=
    fun s hs => by
      rw [hQ, ← Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, hNs s hs, add_zero, hAs s hs]
  have hM : ∀ a b, (((P⁻¹ : GL (Idx D.R.rS D.R.k) (FpX X p)) :
      Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) * A) a b ∈
      p.1.adicCompletionIntegers X.B.I.F := h6
  have hNint : ∀ a b, Nn a b ∈ p.1.adicCompletionIntegers X.B.I.F := by
    intro a b
    rw [hNn]
    show colv (fun _ => 0) z b a ∈ _
    by_cases hb' : IsW b
    · obtain ⟨i, rfl⟩ := hb'
      exact mul_mem hgO (hcc i a)
    · rw [colv_apply_of_not_isW _ _ b hb']
      exact zero_mem _
  have hEint : ∀ a b, (1 + Nn : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) a b ∈
      p.1.adicCompletionIntegers X.B.I.F := by
    intro a b
    rw [Matrix.add_apply, Matrix.one_apply]
    refine add_mem ?_ (hNint a b)
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hEint' : ∀ a b, (1 - Nn : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) a b ∈
      p.1.adicCompletionIntegers X.B.I.F := by
    intro a b
    rw [Matrix.sub_apply, Matrix.one_apply]
    refine sub_mem ?_ (hNint a b)
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hR0 : ∀ a b, ((P⁻¹ * Q : GL (Idx D.R.rS D.R.k) (FpX X p)) :
      Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) a b ∈ p.1.adicCompletionIntegers X.B.I.F := by
    intro a b
    rw [Units.val_mul, hQ, ← Matrix.mul_assoc]
    exact matrix_mul_apply_mem_of_mem _ _ _ hM hEint a b
  have hR0' : ∀ a b, (((P⁻¹ * Q)⁻¹ : GL (Idx D.R.rS D.R.k) (FpX X p)) :
      Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) a b ∈ p.1.adicCompletionIntegers X.B.I.F := by
    intro a b
    rw [Matrix.coe_units_inv, Units.val_mul, hQ, ← Matrix.mul_assoc, Matrix.mul_inv_rev,
      Matrix.inv_eq_right_inv hE1]
    refine matrix_mul_apply_mem_of_mem _ _ _ hEint' ?_ a b
    intro c d
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul]
    have hinv : Ring.inverse (((P⁻¹ : GL (Idx D.R.rS D.R.k) (FpX X p)) :
        Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) * A).det = uu := by
      rw [Ring.inverse_eq_inv]
      exact (eq_inv_of_mul_eq_one_right h8).symm
    rw [hinv]
    exact mul_mem h7 (adjugate_apply_mem_of_forall_mem _ _ hM c d)
  unfold HAdaptQ
  refine ⟨θ, hθ, Q, l, h3, fun s hs => ?_, fun s hs => ?_, ?_, ?_⟩
  · change ((Q⁻¹ : GL (Idx D.R.rS D.R.k) (FpX X p)) :
        Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) *ᵥ cV X u p θ s = Pi.single s 1
    rw [← hQs s hs, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  · change (Q : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p))ᵀ *ᵥ aV X u p θ s =
        l s • Pi.single (dlH s) 1
    have hw : ∀ t, (Aᵀ *ᵥ aV X u p θ s) t =
        colv (cV X u p θ) (yV X hb u p θ) t ⬝ᵥ aV X u p θ s := fun t => by
      rw [hA]
      exact ofCols_transpose_mulVec_apply _ _ t
    have hwn : ∀ t, ¬ IsW t → (Aᵀ *ᵥ aV X u p θ s) t = if t = dlH s then l s else 0 :=
      fun t ht => by
        rw [hw, colv_apply_of_not_isW _ _ t ht, dotProduct_comm_field]
        exact h1 s t hs ht
    have hww : ∀ i, (Aᵀ *ᵥ aV X u p θ s) (wI i) = ((gOf p : ℕ) : FpX X p) * o s i := fun i => by
      rw [hw, dotProduct_comm_field]
      exact h2 s i hs
    have hNT : ∀ (v : Idx D.R.rS D.R.k → FpX X p) t, (Nnᵀ *ᵥ v) t = colv (fun _ => 0) z t ⬝ᵥ v :=
      fun v t => by
        rw [hNn]
        exact ofCols_transpose_mulVec_apply _ _ t
    have hdn := _root_.PIW.MassDataColumns.dlH_frame s hs
    rw [hQ, Matrix.transpose_mul, ← Matrix.mulVec_mulVec]
    funext t
    rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply, hNT]
    by_cases ht : IsW t
    · obtain ⟨i, rfl⟩ := ht
      have hne : (wI i : Idx D.R.rS D.R.k) ≠ dlH s := fun heq => hdn ⟨i, heq.symm⟩
      rw [hww]
      change _ + z i ⬝ᵥ _ = _
      rw [dotProduct_eq_sum_mul, Finset.sum_eq_single (dlH s)]
      · rw [hwn _ hdn, ite_eq_left rfl]
        simp only [z, cc, ite_eq_right hdn, _root_.PIW.MassDataColumns.dlH_dlH, Pi.smul_apply, Pi.single_apply, ite_eq_right hne,
          smul_eq_mul, mul_zero]
        linear_combination (-(((gOf p : ℕ) : FpX X p) * o s i)) * mul_inv_cancel₀ (h3 s hs)
      · intro j _ hj
        by_cases hjW : IsW j
        · rw [hz i j hjW, zero_mul]
        · rw [hwn j hjW, ite_eq_right hj, mul_zero]
      · intro hmem
        exact absurd (Finset.mem_univ _) hmem
    · rw [colv_apply_of_not_isW _ _ t ht, dotProduct_eq_sum_mul, hwn t ht]
      by_cases hts : t = dlH s
      · subst hts
        simp
      · simp [hts]
  · have hQP : Q = P * (P⁻¹ * Q) := (mul_inv_cancel_left P Q).symm
    rw [hQP]
    have hmap : reindex₂ X p (P * (P⁻¹ * Q)) = reindex₂ X p P * reindex₂ X p (P⁻¹ * Q) := by
      unfold reindex₂
      exact map_mul _ _ _
    rw [hmap]
    refine latBasis_mul_of_mem_integers_of_inv_mem X p θ _ _ ?_ ?_ hP
    · intro i j
      first
      | exact hR0 _ _
    · intro i j
      unfold reindex₂
      rw [← map_inv]
      first
      | exact hR0' _ _
  · intro i
    refine ⟨fun t => ⟨cc i t, hcc i t⟩, ?_⟩
    change (Q : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) *ᵥ Pi.single (wI i) 1 -
        yV X hb u p θ i =
      ((gOf p : ℕ) : FpX X p) • ((Q : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) *ᵥ cc i)
    rw [hQ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, hNw,
      hNn, ofCols_colv_zero_mulVec_eq_zero_of_isW z (cc i) (hccW i), add_zero, Matrix.mulVec_add, hAw, add_sub_cancel_left,
      ← Matrix.mulVec_smul]
    try rfl

def AdaptInAll : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (_hK : X.LevelSubgroupCharacter) (u : D.what₂.Word),
    X.MeasTie hb → X.LevelSubgroupNormalized → ∀ p : TypX X, AdaptIn X hb u p

theorem hAdaptAll_of (h : AdaptInAll) : HAdaptAll := by
  unfold HAdaptAll
  intro D X hb hK u hM hL p
  exact hAdaptQ_of_in X hb u p (h X hb hK u hM hL p)

end PIW.MassDataColumns
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.HAdaptRed =====

-- ===== clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.AdaptInDet =====
-- clump-header: {"m": "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.AdaptInDet", "h": "module\n\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.HAdaptRed\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SecondCoordsCongruentMod\nimport Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.SecondProjWeightVectorZero\nimport Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ExistsGlOfLeftInv\nimport Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.FrAIntReindex\nimport Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.MatRMulMatC\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace PIW.MassDataColumns

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl
  MassDataIdxFrA MassDataIdxAdA MassDataIdxSteps Formalism.FourierDecayAlt.S3
open scoped Matrix TensorProduct

variable {D : D7}

section B

variable (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X)
  (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) (P : GL (IdxD D) (FpX X p))

def vT : IdxD D → Fin X.B.I.n → TpX X p
  | Sum.inr (Sum.inl (Sum.inl i)) => adqM X hb u p *ᵥ PI.FinKW.vecV X.B.I p.1 (X.bw i)
  | Sum.inl a => ratV (F := X.B.I.F) (FpX X p) (vecAt (k := D.R.k) (frameOf X u) (Sum.inl a))
  | Sum.inr (Sum.inl (Sum.inr v)) => ratV (F := X.B.I.F) (FpX X p) (vecAt (k := D.R.k) (frameOf X u) (Sum.inr (Sum.inl (Sum.inr v))))
  | Sum.inr (Sum.inr c) => ratV (F := X.B.I.F) (FpX X p) (vecAt (k := D.R.k) (frameOf X u) (Sum.inr (Sum.inr c)))

def mT : Matrix (IdxD D) (IdxD D) (FpX X p) := fun j t => crd1 X p θ P (vT X hb u p t) j

theorem mC_eq :
    ((P⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) *
      ofCols (colv (cV X u p θ) (yV X hb u p θ)) = mT X hb u p θ P := by
  ext j t
  have e : (((P⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) *
      ofCols (colv (cV X u p θ) (yV X hb u p θ))) j t =
      (((P⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) *ᵥ
        colv (cV X u p θ) (yV X hb u p θ) t) j := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, ofCols]
  rw [e]
  rcases t with a | ((i | v) | c) <;> rfl

theorem vT_cong (t : IdxD D) : vT X hb u p t - adqRef X hb u p t ∈ gLam X p := by
  rcases t with a | ((i | v) | c)
  · exact adq_e_cong X hb u p a
  · show adqM X hb u p *ᵥ PI.FinKW.vecV X.B.I p.1 (X.bw i) -
      adqM X hb u p *ᵥ PI.FinKW.vecV X.B.I p.1 (X.bw i) ∈ gLam X p
    rw [sub_self]
    exact zero_mem _
  · exact adq_z_cong X hb u p
  · exact adq_f_cong X hb u p (Fin.rev c)

theorem vT_cong1 (hL : LatBasis X p θ (reindex₂ X p P)) (t j : IdxD D) :
    InG X p (crd1 X p θ P (vT X hb u p t) j - crd1 X p θ P (adqRef X hb u p t) j) :=
  firstCoords_congruent_mod X p θ P hL _ _ (vT_cong X hb u p t) j

theorem vT_int (hL : LatBasis X p θ (reindex₂ X p P)) (t j : IdxD D) :
    crd1 X p θ P (vT X hb u p t) j ∈ OvA X p := by
  have h := (OvA X p).add_mem _ _ (adq_inG_int X p (vT_cong1 X hb u p θ P hL t j))
    (((latCrd_of X p θ P hL _).1 (adq_ref_lat X hb u p t)).1 j)
  rwa [sub_add_cancel] at h

theorem vT_RC (hθ : IsSplitEquiv X p θ) (hε : θ (epsP X p) = (1, 0)) (hL : LatBasis X p θ (reindex₂ X p P))
    (s t : IdxD D) : ∃ z : OvA X p, (adqR X hb u p θ P * mT X hb u p θ P) s t =
      (1 : Matrix (IdxD D) (IdxD D) (FpX X p)) s t + ((gOf p : ℕ) : FpX X p) * (z : FpX X p) := by
  have e1 : (adqR X hb u p θ P * mT X hb u p θ P) s t =
      sgnV X p s * (crd2 X p θ P (adqRefR X hb u p s) ⬝ᵥ crd1 X p θ P (vT X hb u p t)) := by
    simp only [Matrix.mul_apply, adqR, mT, dotProduct, Finset.mul_sum, mul_assoc]
  have hD := adq_dotG X p (a := crd2 X p θ P (adqRefR X hb u p s)) (a' := crd2 X p θ P (adqRefR X hb u p s))
    (b := crd1 X p θ P (vT X hb u p t)) (b' := crd1 X p θ P (adqRef X hb u p t))
    (fun j => ((latCrd_of X p θ P hL _).1 (adq_refR_lat X hb u p s)).2 j)
    (fun j => vT_int X hb u p θ P hL t j) (fun j => by rw [sub_self]; exact inG_zero)
    (fun j => vT_cong1 X hb u p θ P hL t j)
  rw [adq_pairM X hb u p θ P hθ] at hD
  obtain ⟨y, hy⟩ := inG_mul_int _ (sgnV_int X p s) hD
  obtain ⟨z, hz⟩ := rc_cong X p θ P hθ hε hL s t
  refine ⟨y + z, ?_⟩
  rw [e1]
  push_cast
  linear_combination hy + hz

theorem adaptIn_det (hθ : IsSplitEquiv X p θ) (hε : θ (epsP X p) = (1, 0)) (hL : LatBasis X p θ (reindex₂ X p P)) :
    IntO (p.1.adicCompletionIntegers X.B.I.F).toSubring
        (((P⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) *
          ofCols (colv (cV X u p θ) (yV X hb u p θ))) ∧
      ∃ uu : FpX X p, uu ∈ p.1.adicCompletionIntegers X.B.I.F ∧
        (((P⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) *
          ofCols (colv (cV X u p θ) (yV X hb u p θ))).det * uu = 1 := by
  rw [mC_eq X hb u p θ P]
  choose N hN using fun s t => vT_RC X hb u p θ P hθ hε hL s t
  have hgc : ((gA X p : OvA X p) : FpX X p) = ((gOf p : ℕ) : FpX X p) := by simp [gA]
  have hRC : adqR X hb u p θ P * mT X hb u p θ P =
      1 + ((gA X p : OvA X p) : FpX X p) • Matrix.of (fun s t => ((N s t : OvA X p) : FpX X p)) := by
    ext s t
    rw [hN s t, hgc]
    simp
  obtain ⟨c, hc⟩ := exists_gl_of_left_inv (OvA X p) (gA X p) (PIW.MassDataColumns.gOf_nonunit X p)
    (mT X hb u p θ P) (adqR X hb u p θ P) _
    (fun i t => vT_int X hb u p θ P hL t i)
    (fun s i => (OvA X p).mul_mem _ _ (sgnV_int X p s)
      (((latCrd_of X p θ P hL _).1 (adq_refR_lat X hb u p s)).2 i))
    (fun s t => (N s t).2) hRC
  refine ⟨fun i t => vT_int X hb u p θ P hL t i,
    ((((c⁻¹ : GL (IdxD D) (OvA X p)) : Matrix (IdxD D) (IdxD D) (OvA X p)).det : OvA X p) : FpX X p),
    (((c⁻¹ : GL (IdxD D) (OvA X p)) : Matrix (IdxD D) (IdxD D) (OvA X p)).det : OvA X p).2, ?_⟩
  have hdet : (mT X hb u p θ P).det = (((c : Matrix (IdxD D) (IdxD D) (OvA X p)).det : OvA X p) : FpX X p) := by
    rw [← hc]
    exact (RingHom.map_det (OvA X p).subtype (c : Matrix (IdxD D) (IdxD D) (OvA X p))).symm
  have hu : (c : Matrix (IdxD D) (IdxD D) (OvA X p)).det *
      ((c⁻¹ : GL (IdxD D) (OvA X p)) : Matrix (IdxD D) (IdxD D) (OvA X p)).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  rw [hdet]
  have := congrArg (fun x : OvA X p => (x : FpX X p)) hu
  simpa using this

end B

end PIW.MassDataColumns
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.AdaptInDet =====

-- ===== clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.DotPTPinv =====
-- clump-header: {"m": "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.DotPTPinv", "h": "module\n\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.HAdaptRed\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.InGMulInt\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.AdqHRRatV\nimport Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.FrAIntReindex\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SecondCoordsCongruentMod\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.PsiVIteOne\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace PIW.MassDataColumns

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl
  MassDataIdxFrA MassDataIdxAdA MassDataIdxSteps Formalism.FourierDecayAlt.S3
open scoped Matrix TensorProduct

variable {D : D7}

section B

variable (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X)
  (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) (P : GL (IdxD D) (FpX X p))

theorem yV_crd (i : Fin D.R.k) :
    ((P⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) *ᵥ yV X hb u p θ i =
      crd1 X p θ P (adqM X hb u p *ᵥ PI.FinKW.vecV X.B.I p.1 (X.bw i)) := rfl

theorem dot_PT_Pinv (a w : IdxD D → FpX X p) :
    ((P : Matrix (IdxD D) (IdxD D) (FpX X p))ᵀ *ᵥ a) ⬝ᵥ
      (((P⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) *ᵥ w) = a ⬝ᵥ w := by
  rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, Matrix.vecMul_one]

theorem aV_dot (s : IdxD D) (w : IdxD D → FpX X p) :
    aV X u p θ s ⬝ᵥ w = crd2 X p θ P (ratV (F := X.B.I.F) (FpX X p) (vecAt (frameOf X u) s)) ⬝ᵥ
      (((P⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) *ᵥ w) := by
  unfold crd2 aV
  exact (dot_PT_Pinv X p P _ _).symm

theorem ay_gen (hθ : IsSplitEquiv X p θ) (hL : LatBasis X p θ (reindex₂ X p P)) (i : Fin D.R.k)
    (V : Fin X.B.I.n → TpX X p) (v0 : Formalism.L2.SG.HidaSetting.VA X.B.I)
    (hw : adqM X hb u p *ᵥ PI.FinKW.vecV X.B.I p.1 v0 ∈
      latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)))
    (hd : V - adqM X hb u p *ᵥ PI.FinKW.vecV X.B.I p.1 v0 ∈ gLam X p)
    (h0 : ∃ z : OvA X p, crd2 X p θ P (PI.FinKW.vecV X.B.I p.1 v0) ⬝ᵥ
      crd1 X p θ P (PI.FinKW.vecV X.B.I p.1 (X.bw i)) = ((gOf p : ℕ) : FpX X p) * (z : FpX X p)) :
    InG X p (crd2 X p θ P V ⬝ᵥ crd1 X p θ P (adqM X hb u p *ᵥ PI.FinKW.vecV X.B.I p.1 (X.bw i))) := by
  have hyi : ∀ j, crd1 X p θ P (adqM X hb u p *ᵥ PI.FinKW.vecV X.B.I p.1 (X.bw i)) j ∈ OvA X p :=
    fun j => ((latCrd_of X p θ P hL _).1 (adq_ref_lat X hb u p (wI i))).1 j
  have h1 := adq_dotG X p (a := crd2 X p θ P V)
    (a' := crd2 X p θ P (adqM X hb u p *ᵥ PI.FinKW.vecV X.B.I p.1 v0))
    (b := crd1 X p θ P (adqM X hb u p *ᵥ PI.FinKW.vecV X.B.I p.1 (X.bw i)))
    (b' := crd1 X p θ P (adqM X hb u p *ᵥ PI.FinKW.vecV X.B.I p.1 (X.bw i)))
    (fun j => ((latCrd_of X p θ P hL _).1 hw).2 j) hyi
    (secondCoords_congruent_mod X p θ P hL _ _ hd) (fun j => by rw [sub_self]; exact inG_zero)
  rw [adq_pairM X hb u p θ P hθ] at h1
  obtain ⟨z, hz⟩ := h0
  rw [hz] at h1
  have h3 := inG_add h1 (inG_g_mul (X := X) (p := p) z)
  rwa [sub_add_cancel] at h3

theorem ay_inG (hθ : IsSplitEquiv X p θ) (hL : LatBasis X p θ (reindex₂ X p P)) (s : IdxD D) (hs : ¬ IsW s)
    (i : Fin D.R.k) : InG X p (aV X u p θ s ⬝ᵥ yV X hb u p θ i) := by
  rw [aV_dot X u p θ P, yV_crd X hb u p θ P]
  rcases s with a | ((j | v) | c)
  · exact ay_gen X hb u p θ P hθ hL i _ (X.e0 a) (adq_ref_lat X hb u p (Sum.inl a)) (adq_e_cong X hb u p a)
      (fin_dir X p θ P hθ hL _ _ ((X.weightVectorsIntegral i).2.2 a).1)
  · exact absurd ⟨j, rfl⟩ hs
  · exact ay_gen X hb u p θ P hθ hL i _ X.z0 (adq_ref_lat X hb u p zI) (adq_z_cong X hb u p)
      (fin_dir X p θ P hθ hL _ _ (X.weightVectorsIntegral i).1)
  · exact ay_gen X hb u p θ P hθ hL i _ (X.f0 (Fin.rev c)) (adq_refR_lat X hb u p (Sum.inl (Fin.rev c)))
      (adq_f_cong X hb u p (Fin.rev c)) (fin_dir X p θ P hθ hL _ _ ((X.weightVectorsIntegral i).2.2 (Fin.rev c)).2.1)

theorem adaptIn_ay (hθ : IsSplitEquiv X p θ) (hL : LatBasis X p θ (reindex₂ X p P)) :
    ∃ o : IdxD D → Fin D.R.k → FpX X p,
      (∀ s i, ¬ IsW s → aV X u p θ s ⬝ᵥ yV X hb u p θ i = ((gOf p : ℕ) : FpX X p) * o s i) ∧
      (∀ s i, o s i ∈ p.1.adicCompletionIntegers X.B.I.F) := by
  have h : ∀ (s : IdxD D) (i : Fin D.R.k), ∃ y : OvA X p,
      ¬ IsW s → aV X u p θ s ⬝ᵥ yV X hb u p θ i = ((gOf p : ℕ) : FpX X p) * (y : FpX X p) := by
    intro s i
    by_cases hs : IsW s
    · exact ⟨0, fun h => absurd hs h⟩
    · obtain ⟨y, hy⟩ := ay_inG X hb u p θ P hθ hL s hs i
      exact ⟨y, fun _ => hy⟩
  choose o ho using h
  exact ⟨fun s i => (o s i : FpX X p), ho, fun s i => (o s i).2⟩

end B

end PIW.MassDataColumns
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.DotPTPinv =====

-- ===== clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.HacFrame =====
-- clump-header: {"m": "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.HacFrame", "h": "module\n\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.HAdaptRed\nimport Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.CharZeroAdicCompletion\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SecondCoordsCongruentMod\nimport Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SplitLatticeBasisExists\nimport Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.SumKfMulZREqZero\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.FirstCoordsMulVec\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain Formalism.FourierDecayAlt.S3 MassDataIdxSteps MassDataIdxStIm MassDataIdxSpl
open scoped Matrix TensorProduct

variable {D : D7}

section G

variable (X : HidaSetting D) (u : D.what₂.Word) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)

theorem av_cv (hθ : IsSplitEquiv X p θ) (s t : Idx D.R.rS D.R.k) :
    aV X u p θ s ⬝ᵥ cV X u p θ t =
      (θ (inclR (FpX X p) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE X.B.I.cm.sig X.B.I.J (vecAt (frameOf X u) s) (vecAt (frameOf X u) t)))).1 := by
  have h := MassDataIdxSteps.adq_pairR (X := X) (p := p) (θ := θ) (Q := 1) hθ (vecAt (frameOf X u) s) (vecAt (frameOf X u) t)
  unfold aV cV
  simpa only [MassDataIdxSteps.crd1, MassDataIdxSteps.crd2, inv_one, Units.val_one, Matrix.transpose_one, Matrix.one_mulVec] using h

def lF : Idx D.R.rS D.R.k → FpX X p
  | Sum.inr (Sum.inl (Sum.inr _)) =>
      (θ (inclR (FpX X p) (algebraMap X.B.I.F X.B.I.E (-(((D.mem u).A.T : ℕ) : X.B.I.F))))).1
  | _ => 1

theorem hac_frame (hθ : IsSplitEquiv X p θ) (s t : Idx D.R.rS D.R.k) (hs : ¬ IsW s) (ht : ¬ IsW t) :
    aV X u p θ s ⬝ᵥ cV X u p θ t = if t = dlH s then lF X u p θ s else 0 := by
  obtain ⟨hee, hff, hef, hez, hfz, hzz, -⟩ := _root_.MassDataLevelSSteps.FrameW.frameOf_isStd X u
  have hsw := MassDataMassesW.NRatW.hE_swap X
  rw [av_cv X u p θ hθ s t]
  rcases s with a | (i | ⟨⟩) | c
  · rcases t with b | (j | ⟨⟩) | d
    · simp only [vecAt, dlH]
      rw [hee]
      simp
    · exact absurd ⟨j, rfl⟩ ht
    · simp only [vecAt, dlH]
      rw [hez]
      simp
    · simp only [vecAt, dlH, lF]
      rw [hef]
      by_cases h : a = Fin.rev d
      · subst h
        simp
      · have h' : d ≠ Fin.rev a := fun e => h (by rw [e, Fin.rev_rev])
        simp [h, h']
  · exact absurd ⟨i, rfl⟩ hs
  · rcases t with b | (j | ⟨⟩) | d
    · simp only [vecAt, dlH]
      rw [hsw, hez, star_zero]
      simp
    · exact absurd ⟨j, rfl⟩ ht
    · simp only [vecAt, dlH, lF]
      simp only [hzz, ↓reduceIte]
    · simp only [vecAt, dlH]
      rw [hsw, hfz, star_zero]
      simp
  · rcases t with b | (j | ⟨⟩) | d
    · simp only [vecAt, dlH, lF]
      rw [hsw, hef]
      by_cases h : b = Fin.rev c
      · subst h
        simp
      · simp [h]
    · exact absurd ⟨j, rfl⟩ ht
    · simp only [vecAt, dlH]
      rw [hfz]
      simp
    · simp only [vecAt, dlH]
      rw [hff]
      simp

theorem lF_unit (hb : AdBridgeIso X.B.I) (hθ : IsSplitEquiv X p θ) (s : Idx D.R.rS D.R.k) (hs : ¬ IsW s) :
    lF X u p θ s ≠ 0 ∧ (lF X u p θ s)⁻¹ ∈ p.1.adicCompletionIntegers X.B.I.F := by
  rcases s with a | (i | ⟨⟩) | c
  · simp [lF]
  · exact absurd ⟨i, rfl⟩ hs
  · obtain ⟨Q, hQ⟩ := MassDataIdxSteps.exists_GL_latBasis_of_isSplitEquiv X p θ hθ
    have h := MassDataIdxSteps.adq_tau_inv X hb u p θ Q hθ hQ
    have htau : adqTau X u p θ Q = lF X u p θ (Sum.inr (Sum.inl (Sum.inr ()))) := by
      unfold adqTau
      rw [adq_pairR X p θ Q hθ]
      exact congrArg (fun x => (θ (inclR (FpX X p) x)).1) (_root_.MassDataLevelSSteps.FrameW.frameOf_isStd X u).2.2.2.2.2.1
    rw [htau] at h
    exact ⟨h.2, h.1⟩
  · simp [lF]

end G

end PIW.MassDataColumns
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.HacFrame =====

-- ===== clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.AdaptedBasisEveryPlace =====
-- clump-header: {"m": "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.AdaptedBasisEveryPlace", "h": "module\n\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.HAdaptRed\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.AdaptInDet\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.DotPTPinv\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.HacFrame\nimport Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SplitLatticeBasisExists\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain Formalism.FourierDecayAlt.S3 MassDataIdxSteps MassDataIdxStIm MassDataIdxSpl
open scoped Matrix TensorProduct

variable {D : D7}

theorem adaptIn_holds (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X) :
    AdaptIn X hb u p := by
  obtain ⟨θ, hθ, hε⟩ := exists_split_eps X p
  obtain ⟨P, hL⟩ := exists_GL_latBasis_of_isSplitEquiv X p θ hθ
  obtain ⟨o, hay, ho⟩ := adaptIn_ay X hb u p θ P hθ hL
  obtain ⟨hC, uu, huu, hdet⟩ := adaptIn_det X hb u p θ P hθ hε hL
  exact ⟨θ, hθ, P, hL, lF X u p θ, o, uu, fun s t hs ht => hac_frame X u p θ hθ s t hs ht, hay,
    fun s hs => (lF_unit X u p θ hb hθ s hs).1, fun s hs => (lF_unit X u p θ hb hθ s hs).2, ho, hC, huu, hdet⟩

theorem adapted_basis_every_place : AdaptInAll :=
  fun X hb _ u _ _ p => adaptIn_holds X hb u p

end PIW.MassDataColumns
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.AdaptedBasisEveryPlace =====
