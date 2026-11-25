module

public import Formalism.HermitianCurvature.StatementD
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MinLeTruncatedExponential
public import Formalism.HermitianCurvature.StatementTBB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadGermSmoothExtension
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralBoundOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialExhaustion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSettingBis
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTop
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormsJointContinuity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.VecVNonloc
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OnePointBasisFundamentalDomainVolume
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTopVec
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralNormCvecSq
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutBP
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermContinuity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEX_UwTop
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimE
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGCongr
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGInt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGSlice
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutCptDefs
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutDec
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsNormBoundThreeFamilies
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FmSmulLeft
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadContinuityAtZeroOfStandard
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ModuleFormPosCompactSupport
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutFpmDecay
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLowGerm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermMean
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTopB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLemB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimTop
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermConstant
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermRateLowerBound
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LimZeroNPf
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGDegLift
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.VectorIsomorphismCompactSupport
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StandardPairingOfHeads
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OmLongContinuousOn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThetaCompactSupport
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BaseCutoffIsTruncation
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CcCoefMMono
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyZeroNear
import Formalism.HermitianCurvature.HeisenbergConjugationMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BudgetTopConvergence
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LimitOfModuleForms
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSumLeOfForm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGWaveMain
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SizeStandardCompact
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeSumOfCompactCoefficientPositivity

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutCptManual, Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLowAsm, Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLow, Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLowFibre, Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLowGermW, Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTopA, Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTopC, Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTopD, Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTopFields, Formalism.HermitianCurvature.HermitianCurvatureProofs.CutMain, Formalism.HermitianCurvature.HermitianCurvatureProofs.GermContinuityAllLevels, Formalism.HermitianCurvature.HermitianCurvatureProofs.CutMainCpt

-- ===== clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutCptManual =====
-- clump-header: {"m": "Formalism.HermitianCurvature.HermitianCurvatureProofs.CutCptManual", "h": "module\n\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutCptDefs\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockOfChoices\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.FmSmulLeft\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadContinuityAtZeroOfStandard\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.ModuleFormPosCompactSupport\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.SizeAtMinusW\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceCompactSupportCoefficient\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.StandardPairingOfHeads\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace Formalism.FourierDecayAlt.P.TBBx5

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal ComplexOrder

noncomputable section

open Classical

def FormNonnegCpt {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) : Prop :=
  ∀ (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter), KB.CutWord P p.l0 w →
    ∀ (x : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)), PBL.CV (p.T.bs j) x → 0 ≤ p.form j hj w x x

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem formNonneg_ofCpt (hA : P5.ThmPActualCpt) (hFP : PBL.FormPosCpt) (p : KB.Pl P Wp Wq) : FormNonnegCpt p :=
  fun j hj w hw x hx => hFP hA Wp Wq P p j hj w hw x hx

theorem form_csCpt (p : KB.Pl P Wp Wq) (hpos : FormNonnegCpt p) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter)
    (hw : KB.CutWord P p.l0 w) (x y : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
    (hx : PBL.CV (p.T.bs j) x) (hy : PBL.CV (p.T.bs j) y) :
    ‖p.form j hj w x y‖ ^ 2 ≤ (p.form j hj w x x).re * (p.form j hj w y y).re := by

  have hpq : ∀ t : ℂ, 0 ≤ p.form j hj w x x + conj t * p.form j hj w x y + t * p.form j hj w y x +
      t * conj t * p.form j hj w y y := by
    intro t
    have hv : PBL.CV (p.T.bs j) (x + t • y) := PBL.cv_add hx (PBL.cv_smul t hy)
    have h := hpos j hj w hw (x + t • y) hv
    rw [PBL.form_slC (p := p) (j := j) (hj := hj) (w := w) (x₁ := x) (x₂ := y) (y := x + t • y) (c := t)
        (h₁ := hx) (h₂ := hy) (hy := hv),
      PBL.form_srC (p := p) (j := j) (hj := hj) (w := w) (x := x) (y₁ := x) (y₂ := y) (c := t)
        (hx := hx) (h₁ := hx) (h₂ := hy),
      PBL.form_srC (p := p) (j := j) (hj := hj) (w := w) (x := y) (y₁ := x) (y₂ := y) (c := t)
        (hx := hy) (h₁ := hx) (h₂ := hy)] at h
    convert h using 1
    ring
  set A := p.form j hj w x x with hAdef
  set B := p.form j hj w y y with hBdef
  set a := p.form j hj w x y with hadef
  set b := p.form j hj w y x with hbdef
  have key : ∀ t : ℂ, 0 ≤ (A + conj t * a + t * b + t * conj t * B).re ∧
      (A + conj t * a + t * b + t * conj t * B).im = 0 := fun t => by
    have h := Complex.le_def.mp (hpq t)
    exact ⟨by simpa using h.1, by simpa using h.2.symm⟩
  have hA := Complex.le_def.mp (hpos j hj w hw x hx)
  have hB := Complex.le_def.mp (hpos j hj w hw y hy)
  have hAre : 0 ≤ A.re := by simpa using hA.1
  have hBre : 0 ≤ B.re := by simpa using hB.1
  have hAim : A.im = 0 := by simpa using hA.2.symm
  have hBim : B.im = 0 := by simpa using hB.2.symm

  have h1 := (key 1).2
  have h2 := (key Complex.I).2
  simp [hAim, hBim] at h1 h2
  have hbim : b.im = -a.im := by linarith
  have hbre : b.re = a.re := by linarith

  have hs : ∀ s : ℝ, 0 ≤ (‖a‖ ^ 2 * B.re) * (s * s) + (-2 * ‖a‖ ^ 2) * s + A.re := by
    intro s
    have h := (key (-(s : ℂ) * a)).1
    simp [Complex.conj_re, Complex.conj_im, hBim] at h
    rw [hbre, hbim] at h
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith [h]
  have hd := discrim_le_zero hs
  unfold discrim at hd
  have hc0 : 0 ≤ ‖a‖ ^ 2 := sq_nonneg _
  rcases hc0.lt_or_eq with hc | hc
  · have h3 : ‖a‖ ^ 2 * ‖a‖ ^ 2 ≤ ‖a‖ ^ 2 * (A.re * B.re) := by nlinarith
    exact le_of_mul_le_mul_left h3 hc
  · rw [← hc]
    exact mul_nonneg hAre hBre

theorem form_re_nonnegCpt (p : KB.Pl P Wp Wq) (hpos : FormNonnegCpt p) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter)
    (hw : KB.CutWord P p.l0 w) (x : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
    (hx : PBL.CV (p.T.bs j) x) : 0 ≤ (p.form j hj w x x).re := by
  have h := hpos j hj w hw x hx
  exact (Complex.le_def.mp h).1

end place

section lift

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem integral_four_at_place_of_partsCpt (hA : P5.ThmPActualCpt) (hSS : KB.SizeStdCpt) (hDL : KB.DegLift) (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (Λ : ℝ) (K N : ℕ) (hpos : FormNonnegCpt p)
    (hF : KB.CptCoef p.T.base F) (hnn : ∀ y, 0 < nn y) (hgrid : LiftGrid p nn Y Λ K N) :
    TBB.KernelArgumentHypothesisScalar p nn F Y Λ K N := by
  intro b s hb hs hbs h hh w hw hlen t t' ht ht'
  have ha0 : D.IsLocPt (h ++ [(s, t)]) (b + s - 1) := li_locPt h b s t hb hs hh ht
  have ha0' : D.IsLocPt (h ++ [(s, t')]) (b + s - 1) := li_locPt h b s t' hb hs hh ht'
  obtain ⟨grid, hgr⟩ := hgrid b s hb hs hbs w hw hlen
  generalize hJ : b + s - 1 = j at hbs ha0 ha0' grid hgr ⊢

  have hcv : ∀ (w' : List C.Letter) (a0 : C.LPt) (h0 : D.IsLocPt a0 j),
      PBL.CV (p.T.bs j) (KB.slv p.T F j hbs w' a0 h0.2) :=
    fun w' a0 h0 e => Formalism.FourierDecayAlt.P.slice_compact_support_coefficient _ _ P p F j hbs w' a0 h0 hF e
  have hf0 : ∀ (w' : List C.Letter) (a0 : C.LPt) (h0 : D.IsLocPt a0 j), KB.CutWord P p.l0 w' →
      0 ≤ (p.form j hbs w' (KB.slv p.T F j hbs w' a0 h0.2) (KB.slv p.T F j hbs w' a0 h0.2)).re :=
    fun w' a0 h0 hw' => form_re_nonnegCpt p hpos j hbs w' hw' _ (hcv w' a0 h0)
  have hEw0 : ∀ (w' : List C.Letter) (a0 : C.LPt) (h0 : D.IsLocPt a0 j), KB.CutWord P p.l0 w' →
      0 ≤ TBB.Ew p nn F j w' a0 := by
    intro w' a0 h0 hw'
    rw [li_ew p nn F j hbs w' a0 h0]
    exact mul_nonneg (div_nonneg (mul_self_nonneg _) (normC_pos nn hnn w').le) (hf0 w' a0 h0 hw')
  have hc : 0 < TBB.normC nn w := normC_pos nn hnn w

  have key1 : ∀ (sA sA' c R fa fb : ℝ), 0 ≤ sA → 0 ≤ sA' → 0 < c → 0 ≤ fa → 0 ≤ fb → R ^ 2 ≤ fa * fb →
      sA * sA' / c * R ≤ (sA * sA / c * fa + sA' * sA' / c * fb) / 2 := by
    intro sA sA' c R fa fb h1 h2 h3 h4 h5 h6
    have hR : R ≤ Real.sqrt fa * Real.sqrt fb := by
      rw [← Real.sqrt_mul h4]
      exact (le_abs_self R).trans (Real.abs_le_sqrt h6)
    have e1 := Real.sq_sqrt h4
    have e2 := Real.sq_sqrt h5
    have h7 : sA * sA' * R ≤ (sA * sA * fa + sA' * sA' * fb) / 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hR (mul_nonneg h1 h2),
        sq_nonneg (sA * Real.sqrt fa - sA' * Real.sqrt fb)]
    have e3 : sA * sA' / c * R = (sA * sA' * R) / c := by ring
    have e4 : (sA * sA / c * fa + sA' * sA' / c * fb) / 2 = ((sA * sA * fa + sA' * sA' * fb) / 2) / c := by
      ring
    rw [e3, e4]
    exact div_le_div_of_nonneg_right h7 h3.le
  have hcs := form_csCpt p hpos j hbs w hw.1 _ _ (hcv w _ ha0) (hcv w _ ha0')
  have b1 : ‖TBB.NP p nn F j w (h ++ [(s, t)]) (h ++ [(s, t')])‖ ≤
      (TBB.Ew p nn F j w (h ++ [(s, t)]) + TBB.Ew p nn F j w (h ++ [(s, t')])) / 2 := by
    rw [li_np p nn F j hbs w _ _ ha0 ha0', li_ew p nn F j hbs w _ ha0, li_ew p nn F j hbs w _ ha0',
      norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hc.le)]
    exact key1 _ _ _ _ _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hc (hf0 w _ ha0 hw.1)
      (hf0 w _ ha0' hw.1) hcs

  have hnode : ∀ n : Fin K → Fin (2 * (j - s) + s + 1),
      Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, t)])) *
        Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, t')])) / TBB.normC nn w *
        ‖KB.pairJ (p.form j hbs w) (ysOf grid n)
          (KB.slv p.T F j hbs (KB.plusW (ysOf grid n) w) _ ha0.2)
          (KB.slv p.T F j hbs (KB.minusW (ysOf grid n) w) _ ha0'.2)‖ ≤
      Real.sqrt (((ysOf grid n).map nn).prod * ((ysOf grid n).map fun y => nn (y + 1)).prod /
        ((ysOf grid n).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re).prod) *
      Real.sqrt (TBB.Ew p nn F j (KB.plusW (ysOf grid n) w) (h ++ [(s, t)]) *
        TBB.Ew p nn F j (KB.minusW (ysOf grid n) w) (h ++ [(s, t')])) := by
    intro n
    obtain ⟨hcp, hcm, hpw⟩ := hgr.2.2.1 n
    obtain ⟨hq, hSS2⟩ := hSS hA _ _ P p j hbs w (ysOf grid n) hcp hcm hpw
    have hq0 : 0 < ((ysOf grid n).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re).prod := by
      apply List.prod_pos
      intro z hz
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
      exact hq y hy
    have hP1 := prod_map_pos nn hnn (ysOf grid n)
    have hP2 := prod_map_pos (fun y => nn (y + 1)) (fun y => hnn _) (ysOf grid n)
    have hcs2 := hSS2 _ _ (hcv _ _ ha0) (hcv _ _ ha0')
    rw [li_ew p nn F j hbs _ _ ha0, li_ew p nn F j hbs _ _ ha0', normC_plusW, normC_minusW]
    have hsc := scal_cs
      (Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, t)])) *
        Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, t')])) / TBB.normC nn w)
      (Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, t)])) *
        Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, t)])) / TBB.normC nn w)
      (Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, t')])) *
        Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, t')])) / TBB.normC nn w)
      _ _ _ _ _ _
      (div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hc.le)
      (by ring)
      (div_nonneg (mul_self_nonneg _) hc.le) (div_nonneg (mul_self_nonneg _) hc.le)
      hq0 hP1 hP2 (norm_nonneg _) (hf0 _ _ ha0 hcp) (hf0 _ _ ha0' hcm) hcs2
    convert hsc using 3
    all_goals field_simp

  obtain ⟨n₀, hn₀⟩ := sum_le_max
    (fun n : Fin K → Fin (2 * (j - s) + s + 1) => |∏ a, F7.lagCo (grid a) (n a)| *
      Real.sqrt (((ysOf grid n).map nn).prod * ((ysOf grid n).map fun y => nn (y + 1)).prod /
        ((ysOf grid n).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re).prod))
    (fun n => Real.sqrt (TBB.Ew p nn F j (KB.plusW (ysOf grid n) w) (h ++ [(s, t)]) *
        TBB.Ew p nn F j (KB.minusW (ysOf grid n) w) (h ++ [(s, t')])))
    (Λ ^ K) (fun n => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) (fun n => Real.sqrt_nonneg _)
    hgr.2.2.2
  obtain ⟨hcp₀, hcm₀, -⟩ := hgr.2.2.1 n₀
  have b2 : ‖t⁻¹ - t'⁻¹‖ ^ K * ‖TBB.NP p nn F j w (h ++ [(s, t)]) (h ++ [(s, t')])‖ ≤
      Λ ^ K * ((TBB.Ew p nn F j (KB.plusW (ysOf grid n₀) w) (h ++ [(s, t)]) +
        TBB.Ew p nn F j (KB.minusW (ysOf grid n₀) w) (h ++ [(s, t')])) / 2) := by
    have hDL' := hDL _ _ P p F j s hbs w h h t t' ha0 ha0' K grid hF hgr.1
    rw [PBL.rr_eq_form p F j hbs w _ _ ha0 ha0'] at hDL'
    have hnorm : ‖t⁻¹ - t'⁻¹‖ ^ K *
        ‖p.form j hbs w (KB.slv p.T F j hbs w _ ha0.2) (KB.slv p.T F j hbs w _ ha0'.2)‖ ≤
        ∑ n : Fin K → Fin (2 * (j - s) + s + 1), |∏ a, F7.lagCo (grid a) (n a)| *
          ‖KB.pairJ (p.form j hbs w) (ysOf grid n)
            (KB.slv p.T F j hbs (KB.plusW (ysOf grid n) w) _ ha0.2)
            (KB.slv p.T F j hbs (KB.minusW (ysOf grid n) w) _ ha0'.2)‖ := by
      have e : ‖t⁻¹ - t'⁻¹‖ ^ K *
          ‖p.form j hbs w (KB.slv p.T F j hbs w _ ha0.2) (KB.slv p.T F j hbs w _ ha0'.2)‖ =
          ‖((-1 : ℂ) ^ (s - 1) * (t⁻¹ - t'⁻¹)) ^ K *
            p.form j hbs w (KB.slv p.T F j hbs w _ ha0.2) (KB.slv p.T F j hbs w _ ha0'.2)‖ := by
        rw [norm_mul, norm_pow, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      rw [e, hDL']
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rfl
    rw [li_np p nn F j hbs w _ _ ha0 ha0', norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hc.le)]
    have hα0 : 0 ≤ Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, t)])) *
        Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, t')])) / TBB.normC nn w :=
      div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hc.le
    calc ‖t⁻¹ - t'⁻¹‖ ^ K * (Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, t)])) *
          Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, t')])) / TBB.normC nn w *
          ‖p.form j hbs w (KB.slv p.T F j hbs w _ ha0.2) (KB.slv p.T F j hbs w _ ha0'.2)‖)
        = Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, t)])) *
          Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, t')])) / TBB.normC nn w *
          (‖t⁻¹ - t'⁻¹‖ ^ K *
            ‖p.form j hbs w (KB.slv p.T F j hbs w _ ha0.2) (KB.slv p.T F j hbs w _ ha0'.2)‖) := by ring
      _ ≤ Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, t)])) *
          Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, t')])) / TBB.normC nn w *
          ∑ n : Fin K → Fin (2 * (j - s) + s + 1), |∏ a, F7.lagCo (grid a) (n a)| *
            ‖KB.pairJ (p.form j hbs w) (ysOf grid n)
              (KB.slv p.T F j hbs (KB.plusW (ysOf grid n) w) _ ha0.2)
              (KB.slv p.T F j hbs (KB.minusW (ysOf grid n) w) _ ha0'.2)‖ :=
          mul_le_mul_of_nonneg_left hnorm hα0
      _ = ∑ n : Fin K → Fin (2 * (j - s) + s + 1), |∏ a, F7.lagCo (grid a) (n a)| *
            (Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, t)])) *
              Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, t')])) / TBB.normC nn w *
            ‖KB.pairJ (p.form j hbs w) (ysOf grid n)
              (KB.slv p.T F j hbs (KB.plusW (ysOf grid n) w) _ ha0.2)
              (KB.slv p.T F j hbs (KB.minusW (ysOf grid n) w) _ ha0'.2)‖) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun n _ => ?_
          ring
      _ ≤ ∑ n : Fin K → Fin (2 * (j - s) + s + 1), |∏ a, F7.lagCo (grid a) (n a)| *
            Real.sqrt (((ysOf grid n).map nn).prod * ((ysOf grid n).map fun y => nn (y + 1)).prod /
              ((ysOf grid n).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re).prod) *
            Real.sqrt (TBB.Ew p nn F j (KB.plusW (ysOf grid n) w) (h ++ [(s, t)]) *
              TBB.Ew p nn F j (KB.minusW (ysOf grid n) w) (h ++ [(s, t')])) := by
          refine Finset.sum_le_sum fun n _ => ?_
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (hnode n) (abs_nonneg _)
      _ ≤ Λ ^ K * Real.sqrt (TBB.Ew p nn F j (KB.plusW (ysOf grid n₀) w) (h ++ [(s, t)]) *
              TBB.Ew p nn F j (KB.minusW (ysOf grid n₀) w) (h ++ [(s, t')])) := hn₀
      _ ≤ _ := by
          have hl : 0 ≤ Λ ^ K := by
            have hsum0 := hgr.2.2.2
            exact le_trans (Finset.sum_nonneg fun n _ => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) hsum0
          exact mul_le_mul_of_nonneg_left (sqrt_mul_le_avg _ _ (hEw0 _ _ ha0 hcp₀) (hEw0 _ _ ha0' hcm₀)) hl
  rcases mn_pick Λ ‖t⁻¹ - t'⁻¹‖ _ _ _ K (norm_nonneg _) b1 (fun _ => b2) with h1 | h2
  · exact ⟨w, w, isExt_self P p.l0 Y N K w hw (by omega), isExt_self P p.l0 Y N K w hw (by omega), h1⟩
  · have hlenK : (ysOf grid n₀).length = K := by simp [ysOf]
    exact ⟨KB.plusW (ysOf grid n₀) w, KB.minusW (ysOf grid n₀) w,
      isExt_plusW P p.l0 Y N K w (ysOf grid n₀) hlen hlenK (ysOf_mem grid hgr.2.1 n₀) hcp₀,
      isExt_minusW P p.l0 Y N K w (ysOf grid n₀) hlen hlenK (ysOf_mem grid hgr.2.1 n₀) hcm₀, h2⟩

end lift

section wave

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem integral_three_at_place_of_partsCpt (hA : P5.ThmPActualCpt) (hPS : KB.PStdCpt) (hVI : KB.VIsoCpt) (hSS : KB.SizeStdCpt) (hDW : KB.DegWave)
    (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (Λ : ℝ) (K N : ℕ)
    (Cb : ℝ) (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hpos : FormNonnegCpt p) (hF : KB.CptCoef p.T.base F)
    (hnn : ∀ y, 0 < nn y) (hgrid : WaveGrid p nn Y Λ K N) : TBB.KernelFourierIntegralBound p nn F Y Λ K N := by
  intro j hj h hh w hw hlen s
  obtain ⟨grid, hgr⟩ := hgrid j hj w hw hlen
  have hcv : ∀ (w' : List C.Letter), PBL.CV (p.T.bs j) (KB.slv p.T F j hj w' h hh.2) :=
    fun w' e => Formalism.FourierDecayAlt.P.slice_compact_support_coefficient _ _ P p F j hj w' h hh hF e
  have hf0 : ∀ (w' : List C.Letter), KB.CutWord P p.l0 w' →
      0 ≤ (p.form j hj w' (KB.slv p.T F j hj w' h hh.2) (KB.slv p.T F j hj w' h hh.2)).re :=
    fun w' hw' => form_re_nonnegCpt p hpos j hj w' hw' _ (hcv w')
  have hn0 := weighted_auxiliary_norm_nonneg P j hj h hh
  have hEw0 : ∀ (w' : List C.Letter), KB.CutWord P p.l0 w' → 0 ≤ TBB.Ew p nn F j w' h := by
    intro w' hw'
    rw [wv_ew p nn F j hj w' h hh]
    exact mul_nonneg (div_nonneg hn0 (normC_pos nn hnn w').le) (hf0 w' hw')
  have hc : 0 < TBB.normC nn w := normC_pos nn hnn w

  have hVw : ∀ (w' : List C.Letter), KB.CutWord P p.l0 w' →
      PBL.CV (p.T.bs j) (KB.waveG (p.T.bs j) s w' (KB.slv p.T F j hj w' h hh.2)) ∧
      p.form j hj w' (KB.waveG (p.T.bs j) s w' (KB.slv p.T F j hj w' h hh.2))
        (KB.waveG (p.T.bs j) s w' (KB.slv p.T F j hj w' h hh.2)) =
      p.form j hj w' (KB.slv p.T F j hj w' h hh.2) (KB.slv p.T F j hj w' h hh.2) := by
    intro w' hw'
    obtain ⟨h1, h2⟩ := hVI hA _ _ P p j hj w' hw' s _ _ (hcv w') (hcv w')
    exact ⟨h1, h2⟩

  obtain ⟨φ, -, -, hφ, hint⟩ := hPS hA _ _ P p F j hj w h h hh hh Cb hCb hF hw.1
  have hI : ∫ c, P5.fsv s c * TBB.NP p nn F (j + 1) w (h ++ [(1, c)]) (h ++ [(1, c)]) =
      ((C.nAux P.k P.r 0 (fun _ _ => 1) 1 h / TBB.normC nn w : ℝ) : ℂ) *
        p.form j hj w (KB.waveG (p.T.bs j) s w (KB.slv p.T F j hj w h hh.2)) (KB.slv p.T F j hj w h hh.2) := by
    rw [← hint s, ← integral_const_mul]
    refine integral_congr_ae (PBL.ae_ne_zero_complex.mono fun c hc0 => ?_)
    dsimp only
    rw [← wv_np p nn F j hj h hh w c, hφ c hc0]
    ring
  have hα0 : 0 ≤ C.nAux P.k P.r 0 (fun _ _ => 1) 1 h / TBB.normC nn w := div_nonneg hn0 hc.le

  have b1 : ‖∫ c, P5.fsv s c * TBB.NP p nn F (j + 1) w (h ++ [(1, c)]) (h ++ [(1, c)])‖ ≤
      TBB.Ew p nn F j w h := by
    rw [hI, norm_mul, Complex.norm_real, Real.norm_of_nonneg hα0, wv_ew p nn F j hj w h hh]
    refine mul_le_mul_of_nonneg_left ?_ hα0
    have hcs := form_csCpt p hpos j hj w hw.1 _ _ (hVw w hw.1).1 (hcv w)
    rw [(hVw w hw.1).2] at hcs
    have hf := hf0 w hw.1
    nlinarith [norm_nonneg (p.form j hj w (KB.waveG (p.T.bs j) s w (KB.slv p.T F j hj w h hh.2))
      (KB.slv p.T F j hj w h hh.2))]

  have hnode : ∀ n : Fin K → Fin (2 * j + 1),
      C.nAux P.k P.r 0 (fun _ _ => 1) 1 h / TBB.normC nn w *
        ‖KB.pairJ (p.form j hj w) (ysOf grid n)
          (KB.waveG (p.T.bs j) s (KB.plusW (ysOf grid n) w) (KB.slv p.T F j hj (KB.plusW (ysOf grid n) w) h hh.2))
          (KB.slv p.T F j hj (KB.minusW (ysOf grid n) w) h hh.2)‖ ≤
      Real.sqrt (((ysOf grid n).map nn).prod * ((ysOf grid n).map fun y => nn (y + 1)).prod /
        ((ysOf grid n).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re).prod) *
      Real.sqrt (TBB.Ew p nn F j (KB.plusW (ysOf grid n) w) h *
        TBB.Ew p nn F j (KB.minusW (ysOf grid n) w) h) := by
    intro n
    obtain ⟨hcp, hcm, hpw⟩ := hgr.2.2.1 n
    obtain ⟨hq, hSS2⟩ := hSS hA _ _ P p j hj w (ysOf grid n) hcp hcm hpw
    have hq0 : 0 < ((ysOf grid n).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re).prod := by
      apply List.prod_pos
      intro z hz
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
      exact hq y hy
    have hP1 := prod_map_pos nn hnn (ysOf grid n)
    have hP2 := prod_map_pos (fun y => nn (y + 1)) (fun y => hnn _) (ysOf grid n)
    have hcs2 := hSS2 _ _ (hVw _ hcp).1 (hcv _)
    rw [(hVw _ hcp).2] at hcs2
    rw [wv_ew p nn F j hj _ h hh, wv_ew p nn F j hj _ h hh, normC_plusW, normC_minusW]
    have hsc := scal_cs
      (C.nAux P.k P.r 0 (fun _ _ => 1) 1 h / TBB.normC nn w)
      (C.nAux P.k P.r 0 (fun _ _ => 1) 1 h / TBB.normC nn w)
      (C.nAux P.k P.r 0 (fun _ _ => 1) 1 h / TBB.normC nn w)
      _ _ _ _ _ _ hα0 (by ring) hα0 hα0 hq0 hP1 hP2 (norm_nonneg _) (hf0 _ hcp) (hf0 _ hcm) hcs2
    convert hsc using 3
    all_goals field_simp
  obtain ⟨n₀, hn₀⟩ := sum_le_max
    (fun n : Fin K → Fin (2 * j + 1) => |∏ a, F7.lagCo (grid a) (n a)| *
      Real.sqrt (((ysOf grid n).map nn).prod * ((ysOf grid n).map fun y => nn (y + 1)).prod /
        ((ysOf grid n).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re).prod))
    (fun n => Real.sqrt (TBB.Ew p nn F j (KB.plusW (ysOf grid n) w) h *
        TBB.Ew p nn F j (KB.minusW (ysOf grid n) w) h))
    (Λ ^ K) (fun n => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) (fun n => Real.sqrt_nonneg _)
    hgr.2.2.2
  obtain ⟨hcp₀, hcm₀, -⟩ := hgr.2.2.1 n₀
  have b2 : ‖s‖ ^ K * ‖∫ c, P5.fsv s c * TBB.NP p nn F (j + 1) w (h ++ [(1, c)]) (h ++ [(1, c)])‖ ≤
      Λ ^ K * max (TBB.Ew p nn F j (KB.plusW (ysOf grid n₀) w) h)
        (TBB.Ew p nn F j (KB.minusW (ysOf grid n₀) w) h) := by
    have hD := hDW _ _ P p F j hj w h h hh hh K grid s LinearMap.id (fun ε x hx e => hx e) hF hgr.1
    simp_rw [PBL.onOld_id] at hD
    simp only [LinearMap.id_apply] at hD
    have hnorm : ‖s‖ ^ K *
        ‖p.form j hj w (KB.waveG (p.T.bs j) s w (KB.slv p.T F j hj w h hh.2)) (KB.slv p.T F j hj w h hh.2)‖ ≤
        ∑ n : Fin K → Fin (2 * j + 1), |∏ a, F7.lagCo (grid a) (n a)| *
          ‖KB.pairJ (p.form j hj w) (ysOf grid n)
            (KB.waveG (p.T.bs j) s (KB.plusW (ysOf grid n) w)
              (KB.slv p.T F j hj (KB.plusW (ysOf grid n) w) h hh.2))
            (KB.slv p.T F j hj (KB.minusW (ysOf grid n) w) h hh.2)‖ := by
      rw [← norm_pow, ← norm_mul, hD]
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rfl
    have hl : 0 ≤ Λ ^ K :=
      le_trans (Finset.sum_nonneg fun n _ => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) hgr.2.2.2
    rw [hI, norm_mul, Complex.norm_real, Real.norm_of_nonneg hα0]
    calc ‖s‖ ^ K * (C.nAux P.k P.r 0 (fun _ _ => 1) 1 h / TBB.normC nn w *
          ‖p.form j hj w (KB.waveG (p.T.bs j) s w (KB.slv p.T F j hj w h hh.2)) (KB.slv p.T F j hj w h hh.2)‖)
        = C.nAux P.k P.r 0 (fun _ _ => 1) 1 h / TBB.normC nn w * (‖s‖ ^ K *
          ‖p.form j hj w (KB.waveG (p.T.bs j) s w (KB.slv p.T F j hj w h hh.2)) (KB.slv p.T F j hj w h hh.2)‖) := by
          ring
      _ ≤ C.nAux P.k P.r 0 (fun _ _ => 1) 1 h / TBB.normC nn w *
          ∑ n : Fin K → Fin (2 * j + 1), |∏ a, F7.lagCo (grid a) (n a)| *
            ‖KB.pairJ (p.form j hj w) (ysOf grid n)
              (KB.waveG (p.T.bs j) s (KB.plusW (ysOf grid n) w)
                (KB.slv p.T F j hj (KB.plusW (ysOf grid n) w) h hh.2))
              (KB.slv p.T F j hj (KB.minusW (ysOf grid n) w) h hh.2)‖ :=
          mul_le_mul_of_nonneg_left hnorm hα0
      _ = ∑ n : Fin K → Fin (2 * j + 1), |∏ a, F7.lagCo (grid a) (n a)| *
            (C.nAux P.k P.r 0 (fun _ _ => 1) 1 h / TBB.normC nn w *
            ‖KB.pairJ (p.form j hj w) (ysOf grid n)
              (KB.waveG (p.T.bs j) s (KB.plusW (ysOf grid n) w)
                (KB.slv p.T F j hj (KB.plusW (ysOf grid n) w) h hh.2))
              (KB.slv p.T F j hj (KB.minusW (ysOf grid n) w) h hh.2)‖) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun n _ => ?_
          ring
      _ ≤ ∑ n : Fin K → Fin (2 * j + 1), |∏ a, F7.lagCo (grid a) (n a)| *
            Real.sqrt (((ysOf grid n).map nn).prod * ((ysOf grid n).map fun y => nn (y + 1)).prod /
              ((ysOf grid n).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re).prod) *
            Real.sqrt (TBB.Ew p nn F j (KB.plusW (ysOf grid n) w) h *
              TBB.Ew p nn F j (KB.minusW (ysOf grid n) w) h) := by
          refine Finset.sum_le_sum fun n _ => ?_
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (hnode n) (abs_nonneg _)
      _ ≤ Λ ^ K * Real.sqrt (TBB.Ew p nn F j (KB.plusW (ysOf grid n₀) w) h *
              TBB.Ew p nn F j (KB.minusW (ysOf grid n₀) w) h) := hn₀
      _ ≤ _ := mul_le_mul_of_nonneg_left (sqrt_mul_le_max _ _ (hEw0 _ hcp₀) (hEw0 _ hcm₀)) hl
  have hlenK : (ysOf grid n₀).length = K := by simp [ysOf]
  rcases mn_pick Λ ‖s‖ _ _ _ K (norm_nonneg _) b1 (fun _ => b2) with h1 | h2
  · exact ⟨w, isExt_self P p.l0 Y N K w hw (by omega), h1⟩
  · rcases le_total (TBB.Ew p nn F j (KB.minusW (ysOf grid n₀) w) h)
      (TBB.Ew p nn F j (KB.plusW (ysOf grid n₀) w) h) with hle | hle
    · rw [max_eq_left hle] at h2
      exact ⟨KB.plusW (ysOf grid n₀) w,
        isExt_plusW P p.l0 Y N K w (ysOf grid n₀) hlen hlenK (ysOf_mem grid hgr.2.1 n₀) hcp₀, h2⟩
    · rw [max_eq_right hle] at h2
      exact ⟨KB.minusW (ysOf grid n₀) w,
        isExt_minusW P p.l0 Y N K w (ysOf grid n₀) hlen hlenK (ysOf_mem grid hgr.2.1 n₀) hcm₀, h2⟩

end wave

end

end Formalism.FourierDecayAlt.P.TBBx5

theorem Formalism.FourierDecayAlt.P.standard_pairing_of_headsCpt : Formalism.FourierDecayAlt.KB.RadHead → Formalism.FourierDecayAlt.KB.HeadTop → Formalism.FourierDecayAlt.KB.PStdCpt := by
  intro hRH hHT
  first
    | exact fun hP => Formalism.FourierDecayAlt.P.PBO.pStdCpt_of_heads hP hRH hHT

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal ComplexOrder

noncomputable section

open Classical

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem posAt_of_cptCpt (hA : P5.ThmPActualCpt) (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ) (hnn : ∀ y, 0 ≤ nn y)
    (hF : KB.CptCoef p.T.base F) : TBB.PosAt p nn F Y N := by
  refine Formalism.FourierDecayAlt.P.TBBx3.posAt_of_forms p nn F Y N hnn (fun j w h hj hw _ => ?_)
  by_cases hh : D.IsLocPt h j
  · have hrr : p.RR F j w h h =
        p.form j hj w (KB.slv p.T F j hj w h hh.2) (KB.slv p.T F j hj w h hh.2) := by
      unfold KB.Pl.RR D.RRplace
      rw [dite_eq_left ⟨hh, hh⟩, dite_eq_left hj]
      rfl
    rw [hrr]
    have hx := Formalism.FourierDecayAlt.P.module_form_pos_compact_support hA _ _ P p j hj w hw.1 (KB.slv p.T F j hj w h hh.2)
      (fun e => Formalism.FourierDecayAlt.P.slice_compact_support_coefficient _ _ P p F j hj w h hh hF e)
    exact (Complex.le_def.mp hx).1
  · have hrr : p.RR F j w h h = 0 := by
      unfold KB.Pl.RR D.RRplace
      rw [dite_eq_right (fun hc => hh hc.1)]
    rw [hrr]
    simp

theorem truncated_limit_positivity_holdsCpt (hA : P5.ThmPActualCpt) (p : KB.Pl P Wp Wq) {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    (hF : KB.CptCoef p.T.base F) (Y : Finset ℝ) (N : ℕ) : LimPos p F Y N := by
  intro w hw _
  by_cases hh : D.IsLocPt ([] : C.LPt) 0
  · have hrr : p.RR F 0 w [] [] =
        p.form 0 (Nat.zero_le _) w (KB.slv p.T F 0 (Nat.zero_le _) w [] hh.2)
          (KB.slv p.T F 0 (Nat.zero_le _) w [] hh.2) := by
      unfold KB.Pl.RR D.RRplace
      rw [dite_eq_left ⟨hh, hh⟩, dite_eq_left (Nat.zero_le _)]
      rfl
    rw [hrr]
    have hx := Formalism.FourierDecayAlt.P.module_form_pos_compact_support hA _ _ P p 0 (Nat.zero_le _) w hw.1
      (KB.slv p.T F 0 (Nat.zero_le _) w [] hh.2)
      (fun e => Formalism.FourierDecayAlt.P.slice_compact_support_coefficient _ _ P p F 0 (Nat.zero_le _) w [] hh hF e)
    exact (Complex.le_def.mp hx).1
  · have hrr : p.RR F 0 w [] [] = 0 := by
      unfold KB.Pl.RR D.RRplace
      rw [dite_eq_right (fun hc => hh hc.1)]
    rw [hrr]
    simp

end place

end

end Formalism.FourierDecayAlt.P.CutBP
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutCptManual =====

-- ===== clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLowAsm =====
-- clump-header: {"m": "Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLowAsm", "h": "module\n\npublic import Formalism.HermitianCurvature.StatementD\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.MinLeTruncatedExponential\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

end

end Formalism.FourierDecayAlt.P.CutBP
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLowAsm =====

-- ===== clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLow =====
-- clump-header: {"m": "Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLow", "h": "module\n\npublic import Formalism.HermitianCurvature.StatementTBB\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

end

end Formalism.FourierDecayAlt.P.CutBP
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLow =====

-- ===== clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLowFibre =====
-- clump-header: {"m": "Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLowFibre", "h": "module\n\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLow\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadGermSmoothExtension\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralBoundOfParts\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.MinLeTruncatedExponential\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialExhaustion\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.StandardPairingOfHeads\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt MeasureTheory
open scoped ComplexConjugate

noncomputable section

open Classical

end

end Formalism.FourierDecayAlt.P.CutBP
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLowFibre =====

-- ===== clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLowGermW =====
-- clump-header: {"m": "Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLowGermW", "h": "module\n\npublic import Formalism.HermitianCurvature.StatementTBB\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSettingBis\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutBP.GLG

open Formalism.FourierDecayAlt

noncomputable section

end

end Formalism.FourierDecayAlt.P.CutBP.GLG
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLowGermW =====

-- ===== clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTopA =====
-- clump-header: {"m": "Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTopA", "h": "module\n\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTop\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormsJointContinuity\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.OmLongContinuousOn\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.ThetaCompactSupport\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.VecVNonloc\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutBP.GT

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

end

end Formalism.FourierDecayAlt.P.CutBP.GT
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTopA =====

-- ===== clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTopC =====
-- clump-header: {"m": "Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTopC", "h": "module\n\npublic import Formalism.HermitianCurvature.StatementTBB\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSettingBis\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.OnePointBasisFundamentalDomainVolume\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutBP.GT

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

end

end Formalism.FourierDecayAlt.P.CutBP.GT
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTopC =====

-- ===== clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTopD =====
-- clump-header: {"m": "Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTopD", "h": "module\n\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTopVec\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralNormCvecSq\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Ring.IsFormallyReal\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutBP.GT

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

end

end Formalism.FourierDecayAlt.P.CutBP.GT
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTopD =====

-- ===== clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTopFields =====
-- clump-header: {"m": "Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTopFields", "h": "module\n\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTopVec\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralNormCvecSq\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Ring.IsFormallyReal\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Separation.CompletelyRegular\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutBP.GT

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {I : Type} [Fintype I]
  {p : KB.Pl P Wp Wq} {nn : ℝ → ℝ} {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} {w : List C.Letter} {c : I → ℝ}
  {Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp)} {L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq}

end place


section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {I : Type} [Fintype I]
  {p : KB.Pl P Wp Wq} {nn : ℝ → ℝ} {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} {w : List C.Letter} {c : I → ℝ}
  {Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp)} {L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq}

end place

end

end Formalism.FourierDecayAlt.P.CutBP.GT
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTopFields =====

-- ===== clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutMain =====
-- clump-header: {"m": "Formalism.HermitianCurvature.HermitianCurvatureProofs.CutMain", "h": "module\n\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutBP\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants

noncomputable section

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem amaps_id (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b : ℝ) :
    Amaps p f (fun _ => ContinuousLinearMap.id ℂ Wq) (fun _ => ContinuousLinearMap.id ℂ Wq)
      (fun _ => ContinuousLinearMap.id ℂ Wq) (fun _ => ContinuousLinearMap.id ℂ Wq) b 0 := by
  refine ⟨fun γ _ _ => by simp, fun γ _ _ => by simp, fun γ _ _ v => ?_, fun γ _ _ => ?_, fun γ _ _ => ?_⟩
  · simp only [mul_zero, pow_zero, one_mul, ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply]
    nlinarith [sq_nonneg ‖v‖]
  · rw [pow_zero]
    exact pow_le_one₀ (norm_nonneg _) ContinuousLinearMap.norm_id_le
  · rw [pow_zero]
    exact pow_le_one₀ (norm_nonneg _) ContinuousLinearMap.norm_id_le

end place


end

end Formalism.FourierDecayAlt.P.CutBP
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutMain =====

-- ===== clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.GermContinuityAllLevels =====
-- clump-header: {"m": "Formalism.HermitianCurvature.HermitianCurvatureProofs.GermContinuityAllLevels", "h": "module\n\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermContinuity\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.BaseCutoffIsTruncation\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.CcCoefMMono\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEX_UwTop\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimE\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormsJointContinuity\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyZeroNear\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGCongr\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGInt\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGSlice\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal

noncomputable section

end

end Formalism.FourierDecayAlt.P.CutBP
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.GermContinuityAllLevels =====

-- ===== clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutMainCpt =====
-- clump-header: {"m": "Formalism.HermitianCurvature.HermitianCurvatureProofs.CutMainCpt", "h": "module\n\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutCptDefs\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutDec\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTopVec\nimport Formalism.HermitianCurvature.HeisenbergConjugationMeasurePreserving\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.BaseCutoffIsTruncation\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.BudgetTopConvergence\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSettingBis\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutCptManual\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutFpmDecay\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLowAsm\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLowFibre\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLowGerm\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLowGermW\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermMean\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTopA\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTopB\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTopC\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTopD\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTopFields\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLemB\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimTop\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutMain\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermConstant\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermContinuityAllLevels\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermRateLowerBound\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadContinuityAtZeroOfStandard\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadGermSmoothExtension\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralBoundOfParts\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.LimZeroNPf\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.LimitOfModuleForms\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.MinLeTruncatedExponential\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.ModuleFormPosCompactSupport\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSumLeOfForm\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGDegLift\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGWaveMain\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialExhaustion\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.SizeStandardCompact\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.VectorIsomorphismCompactSupport\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Algebra.Ring.IsFormallyReal\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Separation.CompletelyRegular\nimport Mathlib.Topology.Sheaves.Presheaf\nimport Std.Tactic.BVDecide.Normalize.Prop\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermContinuity\nimport Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeSumOfCompactCoefficientPositivity\n"}
section -- clump:auto
@[expose] public section

namespace Formalism.FourierDecayAlt.P.TBBx3
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal
noncomputable section
variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem _root_.Formalism.FourierDecayAlt.P.TBBx3.head_continuity_at_zero_of_standardCpt (hPS : KB.PStdCpt) (hTP : P5.ThmPActualCpt) (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ) (Cb : ℝ)
    (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hF : KB.CptCoef p.T.base F) : TBB.HeadContinuityAtZero p nn F Y N := by
  intro j hj h hh w hw hN
  obtain ⟨φ, hφc, hφi, hφ, -⟩ := hPS hTP Wp Wq P p F j hj w h h hh hh Cb hCb hF hw.1
  set A := C.nAux P.k P.r 0 (fun _ _ => 1) 1 h with hAdef
  refine ⟨fun c => ((A / TBB.normC nn w : ℝ) : ℂ) * φ c, continuous_const.mul hφc, hφi.const_mul _, ?_⟩
  intro c hc
  simp only
  rw [hφ c hc]
  have hA : 0 ≤ A := Formalism.FourierDecayAlt.P.PBD.lpt_value_nonneg_of_pos_of_size_le P.k P.r 0 (fun _ _ => 1) (fun _ _ => one_pos) h 1 le_rfl
    (by rw [hh.2]; omega)
  have hn : TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(1, c)]) =
      A * C.nAux P.k P.r (D.ptGG (TBB.TTp p) (h ++ [(1, c)])) (fun _ _ => 1) (1 + j) [(1, c)] := by
    unfold TBB.nPt
    rw [Formalism.FourierDecayAlt.P.PBD.weight_product_append, hh.2, hAdef,
      Formalism.FourierDecayAlt.P.PBD.weight_product_indep_of_real_parameter P.k P.r _ 0 (fun _ _ => 1) h 1 le_rfl (by rw [hh.2]; omega)]
  unfold TBB.NP
  rw [hn]
  by_cases hjr : j = P.r
  · subst hjr
    by_cases hc2 : Complex.normSq c ≤ Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z'
    · have h0 : p.RR F (P.r + 1) w (h ++ [(1, c)]) (h ++ [(1, c)]) = 0 :=
        Formalism.FourierDecayAlt.P.PBD.rrTop_zero P p.l0 p.T p.ν' p.m₀ p.Θ p.TP (M.sgn P p.l0) F w h _ c hh.2 hc2
      rw [h0]
      simp
    · push Not at hc2
      have hT : Tz P.k P.r p.T.base.z = P.T := p.hP.2.2.2.1
      have hT' : Tz P.k P.r p.T.base.z' = P.T' := p.hP.2.2.2.2.1
      have hlast : D.ptGG (TBB.TTp p) (h ++ [(1, c)]) = Complex.normSq c - TBB.TTp p := by
        simp [D.ptGG, D.ptLast]
      have hTT : TBB.TTp p = P.T * P.T' := by
        unfold TBB.TTp
        rw [hT, hT']
      have hfac : C.nAux P.k P.r (D.ptGG (TBB.TTp p) (h ++ [(1, c)])) (fun _ _ => 1) (1 + P.r) [(1, c)] =
          KB.levW P (P.r + 1) c := by
        rw [hlast, hTT]
        rw [hT, hT'] at hc2
        simp only [C.nAux, KB.levW, B2.zWeight, ite_eq_left hc2.le]
        rw [ite_eq_left ⟨by omega, trivial⟩]
        simp
      have hlev : 0 ≤ KB.levW P (P.r + 1) c := by
        rw [← hfac, hlast]
        simp only [C.nAux]
        rw [ite_eq_left ⟨by omega, trivial⟩]
        have : 0 ≤ Complex.normSq c - TBB.TTp p := by
          unfold TBB.TTp; linarith
        simpa using pow_nonneg this _
      rw [hfac, Real.mul_self_sqrt (mul_nonneg hA hlev)]
      push_cast
      ring
  · have hfac : C.nAux P.k P.r (D.ptGG (TBB.TTp p) (h ++ [(1, c)])) (fun _ _ => 1) (1 + j) [(1, c)] =
        KB.levW P (j + 1) c := by
      simp only [C.nAux, KB.levW]
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      have e : 1 + j + 1 - 1 = j + 1 := by omega
      rw [e]
      simp only [one_mul, mul_one, Nat.cast_one]
      congr 1
      ring
    have hlev : 0 ≤ KB.levW P (j + 1) c := by
      simp only [KB.levW]
      rw [ite_eq_right (by omega)]
      exact zpow_nonneg (norm_nonneg _) _
    rw [hfac, Real.mul_self_sqrt (mul_nonneg hA hlev)]
    push_cast
    ring

end
end Formalism.FourierDecayAlt.P.TBBx3

namespace Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

theorem _root_.Formalism.FourierDecayAlt.P.head_continuity_at_zero_of_compact_coefficientsCpt (hPS : KB.PStdCpt) (hTP : P5.ThmPActualCpt) {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
    [FiniteDimensional ℂ Wq] {P : M.Par} (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (Y : Finset ℝ) (N : ℕ) (Cb : ℝ) (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hF : KB.CptCoef p.T.base F) :
    Formalism.FourierDecayAlt.TBB.HeadContinuityAtZero p nn F Y N := by
  exact TBBx3.head_continuity_at_zero_of_standardCpt hPS hTP p nn F Y N Cb hCb hF

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.CutBP
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology
noncomputable section

theorem _root_.Formalism.FourierDecayAlt.P.CutBP.limPos_of_limEvTCpt (hA : P5.ThmPActualCpt) (Cb : ℝ) : ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
    [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ)
    (A : ℝ) (N : ℕ) (Y : Finset ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → B.CkOn ⊤ (B.GV P.k P.r) F → (∀ m : ℕ, B.InCC A m F) →
    Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
    LimEvT p χ F Y N → LimPos p F Y N := by
  obtain ⟨Cc, hCc⟩ := Formalism.FourierDecayAlt.P.limit_of_module_forms Cb
  refine ⟨Cc, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p F χ A N Y hDD hχ hF hFA hth hEv w hw hN
  have hcut : ∀ ε : ℝ, 0 < ε → 0 ≤ (p.RR (D.cutF p.T.base χ F ε) 0 w [] []).re := by
    intro ε hε
    obtain ⟨hcpt, hlim⟩ := hCc Wp Wq P p F χ ε A N (cutN P.k P.r) hDD hχ hε hF hFA hth (fun _ _ => rfl)
    have hT := (Complex.continuous_re.tendsto _).comp (hlim 0 w hw.1 hN [] [])
    exact ge_of_tendsto hT (Eventually.of_forall fun n => truncated_limit_positivity_holdsCpt hA p (hcpt n) Y N w hw hN)
  exact ge_of_tendsto (hEv w hw hN) (eventually_nhdsWithin_of_forall fun ε hε => hcut ε hε)

end
end Formalism.FourierDecayAlt.P.CutBP

namespace Formalism.FourierDecayAlt.P.CutBP
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology
noncomputable section

theorem _root_.Formalism.FourierDecayAlt.P.CutBP.limE_of_limEvTCpt (hA : P5.ThmPActualCpt) (Cb : ℝ) : ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
    [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ nn : ℝ → ℝ)
    (A : ℝ) (N : ℕ) (Y : Finset ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → (∀ y, 0 ≤ nn y) → B.CkOn ⊤ (B.GV P.k P.r) F →
    (∀ m : ℕ, B.InCC A m F) →
    Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
    LimEvT p χ F Y N → LimBd p nn F Y N → LimE p nn χ F Y N := by
  obtain ⟨Cc, hC⟩ := limPos_of_limEvTCpt hA Cb
  refine ⟨Cc, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p F χ nn A N Y h1 h2 h3 h4 h5 h6 hEv hBd
  exact limE_of_partsT p nn χ F Y N h3 hEv (hC Wp Wq P p F χ A N Y h1 h2 h4 h5 h6 hEv) hBd

end
end Formalism.FourierDecayAlt.P.CutBP

namespace Formalism.FourierDecayAlt.P.TBBx5
open Formalism.FourierDecayAlt

theorem _root_.Formalism.FourierDecayAlt.P.TBBx5.integral_four_of_parts_holdsCpt : IntegralFourFromComponentsCpt := by
  intro hA hSS hDL hFP Wp Wq _ _ _ _ _ _ P p nn F Y Λ K N hF hnn hgrid
  exact integral_four_at_place_of_partsCpt hA hSS hDL p nn F Y Λ K N (formNonneg_ofCpt hA hFP p) hF hnn hgrid

end Formalism.FourierDecayAlt.P.TBBx5

namespace Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt

theorem _root_.Formalism.FourierDecayAlt.P.integral_four_at_placeCpt (hA : P5.ThmPActualCpt) (hSS : KB.SizeStdCpt) (hDL : KB.DegLift) (hFP : PBL.FormPosCpt)
    {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par} (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (Λ : ℝ) (K N : ℕ)
    (hF : KB.CptCoef p.T.base F) (hnn : ∀ y, 0 < nn y) (hgrid : TBBx5.LiftGrid p nn Y Λ K N) :
    Formalism.FourierDecayAlt.TBB.KernelArgumentHypothesisScalar p nn F Y Λ K N := TBBx5.integral_four_of_parts_holdsCpt hA hSS hDL hFP Wp Wq P p nn F Y Λ K N hF hnn hgrid

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.TBBx5
open Formalism.FourierDecayAlt

theorem _root_.Formalism.FourierDecayAlt.P.TBBx5.integral_three_of_parts_holdsCpt : CurvatureIntegralOfPartsCpt := by
  intro hA hPS hVI hSS hDW hFP Wp Wq _ _ _ _ _ _ P p nn F Y Λ K N Cb hCb hF hnn hgrid
  exact integral_three_at_place_of_partsCpt hA hPS hVI hSS hDW p nn F Y Λ K N Cb hCb (formNonneg_ofCpt hA hFP p) hF hnn hgrid

end Formalism.FourierDecayAlt.P.TBBx5

namespace Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt

theorem _root_.Formalism.FourierDecayAlt.P.integral_three_at_placeCpt (hA : P5.ThmPActualCpt) (hPS : KB.PStdCpt) (hVI : KB.VIsoCpt) (hSS : KB.SizeStdCpt)
    (hDW : KB.DegWave) (hFP : PBL.FormPosCpt) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
    (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (Λ : ℝ) (K N : ℕ)
    (Cb : ℝ) (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hF : KB.CptCoef p.T.base F) (hnn : ∀ y, 0 < nn y)
    (hgrid : TBBx5.WaveGrid p nn Y Λ K N) : Formalism.FourierDecayAlt.TBB.KernelFourierIntegralBound p nn F Y Λ K N := TBBx5.integral_three_of_parts_holdsCpt hA hPS hVI hSS hDW hFP Wp Wq P p nn F Y Λ K N Cb hCb hF hnn hgrid

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.CutBP
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal
noncomputable section
section place
variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem _root_.Formalism.FourierDecayAlt.P.CutBP.corS_of_cptCpt (hA : P5.ThmPActualCpt) (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (Y : Finset ℝ) (Λ : ℝ) (K N : ℕ) (Cb C₂ : ℝ)
    (hLS : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
      (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (Λ : ℝ) (K N : ℕ), 3 ≤ K → 1 ≤ Λ →
      TBB.PosAt p nn F Y N → TBB.HeadContinuityAtZero p nn F Y N → TBB.KernelFourierIntegralBound p nn F Y Λ K N → TBB.KernelArgumentHypothesisScalar p nn F Y Λ K N →
      TBB.BlockGrowthBound p nn F Y K N → TBB.LemmaS p nn F Y Λ K N C₂)
    (hC₂ : 0 ≤ C₂) (hK : 3 ≤ K) (hKN : (P.r + 1) * K ≤ N) (hΛ : 1 ≤ Λ) (hnn : ∀ y, 0 < nn y)
    (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hG : KB.CptCoef p.T.base G)
    (hWG : TBBx5.WaveGrid p nn Y Λ K N) (hLG : TBBx5.LiftGrid p nn Y Λ K N) (hI5 : TBB.BlockGrowthBound p nn G Y K N) :
    TBB.CorS p nn G Y Λ K N C₂ := by
  have hPS : KB.PStdCpt := Formalism.FourierDecayAlt.P.standard_pairing_of_headsCpt Formalism.FourierDecayAlt.P.radial_head Formalism.FourierDecayAlt.P.head_top
  have hPos : TBB.PosAt p nn G Y N := posAt_of_cptCpt hA p nn G Y N (fun y => (hnn y).le) hG
  have hI2 := Formalism.FourierDecayAlt.P.head_continuity_at_zero_of_compact_coefficientsCpt hPS hA p nn G Y N Cb hCb hG
  have hI3 := Formalism.FourierDecayAlt.P.integral_three_at_placeCpt hA hPS Formalism.FourierDecayAlt.P.vector_isomorphism_compact_support Formalism.FourierDecayAlt.P.size_standard_compact
    Formalism.FourierDecayAlt.P.degree_of_plane_wave (Formalism.FourierDecayAlt.P.module_form_pos_compact_support : PBL.FormPosCpt) p nn G Y Λ K N Cb hCb hG hnn hWG
  have hI4 := Formalism.FourierDecayAlt.P.integral_four_at_placeCpt hA Formalism.FourierDecayAlt.P.size_standard_compact Formalism.FourierDecayAlt.P.degree_of_lift_pairing
    (Formalism.FourierDecayAlt.P.module_form_pos_compact_support : PBL.FormPosCpt) p nn G Y Λ K N hG hnn hLG
  exact Formalism.FourierDecayAlt.P.corSOfLemmaS_statement Wp Wq P p nn G Y Λ K N C₂ hKN hC₂ hPos
    (hLS Wp Wq P p nn G Y Λ K N hK hΛ hPos hI2 hI3 hI4 hI5)

end place
end
end Formalism.FourierDecayAlt.P.CutBP

namespace Formalism.FourierDecayAlt.P.CutBP
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal
noncomputable section

theorem _root_.Formalism.FourierDecayAlt.P.CutBP.ptBound_dec_allCpt (hA : P5.ThmPActualCpt) : ∃ C₂ : ℝ, 0 < C₂ ∧
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
      (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Λ κ₀ : ℝ) (χ nn : ℝ → ℝ) (Y : Finset ℝ) (K N : ℕ) (Cb : ℝ),
      1 ≤ Λ → 0 < κ₀ → 3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nn y) →
      KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → B.CkOn ⊤ (B.GV P.k P.r) F →
      TBBx5.WaveGrid p nn Y Λ K N → TBBx5.LiftGrid p nn Y Λ K N →
      (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound p nn (apx (D.cutF p.T.base χ F ε) n) Y K N) →
      (∀ ε : ℝ, 0 < ε → LimTopN p nn (D.cutF p.T.base χ F ε)) →
      (∀ ε : ℝ, 0 < ε → LimZeroN p nn (D.cutF p.T.base χ F ε) Y N) →
      LimE p nn χ F Y N → LemB p F κ₀ → TBB.PtBound p F (κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1)) := by
  obtain ⟨C₂, hC₂, hLS⟩ :=
    Formalism.FourierDecayAlt.Final.tbb_lemmaSOfSteps Formalism.FourierDecayAlt.Final.tbb_stepOne Formalism.FourierDecayAlt.Final.tbb_stepUp
  refine ⟨C₂, hC₂, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p F Λ κ₀ χ nn Y K N Cb hΛ hκ hK hKN hχ hnn hCb hF hWG hLG hI5 hT hZ hE hB
  refine Formalism.FourierDecayAlt.Final.tbb_ptBoundOfCorS Wp Wq P p nn χ F Y Λ K N C₂ κ₀ hC₂.le hκ hnn
    ⟨1, one_pos, fun ε hε _ => ?_⟩ (TBBx3.vecCutAt_of_one p χ F hχ.2.2)
    (TBBx3.limZeroAt_of_limits p nn χ F Y N κ₀ hE hB)
  refine corS_of_apx p nn _ Y Λ K N C₂ (fun n => ?_) (hT ε hε) (hZ ε hε)
  exact corS_of_cptCpt hA p nn _ Y Λ K N Cb C₂ hLS hC₂.le hK hKN hΛ hnn hCb
    (cptCoef_apx P p.T.base hχ hF hε n) hWG hLG (hI5 ε hε n)

end
end Formalism.FourierDecayAlt.P.CutBP

namespace Formalism.FourierDecayAlt.P.CutBP
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal
noncomputable section

theorem _root_.Formalism.FourierDecayAlt.P.CutBP.thmBpAt_of_leaves_decCpt (hA : P5.ThmPActualCpt) (C₃ CΛ C₀ Cκ : ℝ) (hC₃ : 0 ≤ C₃) (hCΛ : 0 ≤ CΛ)
    (hC₀ : 1 / 2 ≤ C₀) :
    ∃ C₄ : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
      (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Ap Am : B.Mat P.k P.r → (Wq →L[ℂ] Wq))
      (ApPt AmPt : C.LPt → (Wq →L[ℂ] Wq)) (b Λ κ₀ : ℝ) (n₀ p₀ : ℕ) (χ nn : ℝ → ℝ) (Y : Finset ℝ) (K N : ℕ)
      (Cb : ℝ),
      3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → 0 < κ₀ →
      κ₀ ≤ b ^ (Cκ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2) → 1 ≤ TBB.Tq p →
      n₀ ≤ 30 * (P.r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * (3 * ((P.r : ℝ) + 1)) + 1 →
      3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nn y) →
      KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → B.CkOn ⊤ (B.GV P.k P.r) f →
      B.CkOn ⊤ (B.GV P.k P.r) Ap → B.CkOn ⊤ (B.GV P.k P.r) Am →
      Amaps p f Ap Am ApPt AmPt b n₀ → BigCellDerivativeExpansion p f b C₃ (2 * p₀ + n₀) →
      TBBx5.WaveGrid p nn Y Λ K N → TBBx5.LiftGrid p nn Y Λ K N →
      (∀ ε : ℝ, 0 < ε → ∀ n : ℕ,
        TBB.BlockGrowthBound p nn (apx (D.cutF p.T.base χ (TBBx4.fpm p f Ap p₀) ε) n) Y K N) →
      (∀ ε : ℝ, 0 < ε → ∀ n : ℕ,
        TBB.BlockGrowthBound p nn (apx (D.cutF p.T.base χ (TBBx4.fpm p f Am p₀) ε) n) Y K N) →
      (∀ ε : ℝ, 0 < ε → LimTopN p nn (D.cutF p.T.base χ (TBBx4.fpm p f Ap p₀) ε)) →
      (∀ ε : ℝ, 0 < ε → LimTopN p nn (D.cutF p.T.base χ (TBBx4.fpm p f Am p₀) ε)) →
      (∀ ε : ℝ, 0 < ε → LimZeroN p nn (D.cutF p.T.base χ (TBBx4.fpm p f Ap p₀) ε) Y N) →
      (∀ ε : ℝ, 0 < ε → LimZeroN p nn (D.cutF p.T.base χ (TBBx4.fpm p f Am p₀) ε) Y N) →
      LimE p nn χ (TBBx4.fpm p f Ap p₀) Y N → LimE p nn χ (TBBx4.fpm p f Am p₀) Y N →
      LemB p (TBBx4.fpm p f Ap p₀) κ₀ → LemB p (TBBx4.fpm p f Am p₀) κ₀ →
      TBB.ThmBpAt p f b C₄ n₀ p₀ := by
  obtain ⟨C₂, hC₂, hPB⟩ := ptBound_dec_allCpt hA
  obtain ⟨C₄, hC₄⟩ := Formalism.FourierDecayAlt.Final.tbb_thmBpOfParts C₃ CΛ C₀ C₂ Cκ hC₃ hCΛ hC₀ hC₂
  refine ⟨C₄, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f Ap Am ApPt AmPt b Λ κ₀ n₀ p₀ χ nn Y K N Cb hb hΛ hΛb hκ hκb hTq hn₀
    hp₀ hK hKN hχ hnn hCb hf hAp hAm hAm' hExp hWG hLG hI5p hI5m hTp hTm hZp hZm hEp hEm hBp hBm
  obtain ⟨h1, h2, h3, h4, h5⟩ := hAm'
  exact hC₄ Wp Wq P p f (TBBx4.fpm p f Ap p₀) (TBBx4.fpm p f Am p₀) b Λ κ₀ n₀ p₀ hb hΛ hΛb hκ hκb
    hTq hn₀ hp₀ (TBBx4.normAt_fpm p f Ap Am ApPt AmPt b n₀ p₀ h1 h2 h3 h4 h5)
    (hPB Wp Wq P p _ Λ κ₀ χ nn Y K N Cb hΛ hκ hK hKN hχ hnn hCb (ckOn_fpm p p₀ hf hAp) hWG hLG
      hI5p hTp hZp hEp hBp)
    (hPB Wp Wq P p _ Λ κ₀ χ nn Y K N Cb hΛ hκ hK hKN hχ hnn hCb (ckOn_fpm p p₀ hf hAm) hWG hLG
      hI5m hTm hZm hEm hBm)
    (TBBx4.regularity_at_place_of_expansion p f b C₃ (2 * p₀ + n₀) (by linarith) hExp)

end
end Formalism.FourierDecayAlt.P.CutBP

namespace Formalism.FourierDecayAlt.P.CutBP
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants
noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem _root_.Formalism.FourierDecayAlt.P.CutBP.thmBpAt_mainCpt (hA : P5.ThmPActualCpt) (Cb C₃ CΛ C₀ Cκ : ℝ) (hC₃ : 0 ≤ C₃) (hCΛ : 0 ≤ CΛ) (hC₀ : 1 / 2 ≤ C₀) :
    ∃ C₄ c₃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
      (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b Λ κ₀ A₀ : ℝ) (p₀ : ℕ) (χ nn : ℝ → ℝ) (Y : Finset ℝ) (K N : ℕ),
      3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → 0 < κ₀ →
      κ₀ ≤ b ^ (Cκ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2) → 1 ≤ TBB.Tq p →
      (p₀ : ℝ) ≤ C₀ * (3 * ((P.r : ℝ) + 1)) + 1 →
      3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nn y) →
      KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) →
      c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      BigCellDerivativeExpansion p f b C₃ (2 * p₀ + 0) →
      TBBx5.WaveGrid p nn Y Λ K N → TBBx5.LiftGrid p nn Y Λ K N →
      (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound p nn
        (apx (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) n) Y K N) →
      LimE p nn χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) Y N →
      LemB p (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) κ₀ →
      TBB.ThmBpAt p f b C₄ 0 p₀ := by
  obtain ⟨C₄, hC₄⟩ := thmBpAt_of_leaves_decCpt hA C₃ CΛ C₀ Cκ hC₃ hCΛ hC₀
  obtain ⟨c₃, hc₃⟩ := limTopN_cut_of_inCC
  obtain ⟨Cc, hCc⟩ := limZeroN_of_formLimit Cb
  refine ⟨C₄, c₃, Cc, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f b Λ κ₀ A₀ p₀ χ nn Y K N hb hΛ hΛb hκ hκb hT hp₀ hK hKN hχ hnn hCb hf hfA hth1 hth2
    hexp hWG hLG hI5 hE hB
  have hid : B.CkOn ⊤ (B.GV P.k P.r) (fun _ : B.Mat P.k P.r => ContinuousLinearMap.id ℂ Wq) := fun g₀ _ =>
    ⟨Set.univ, fun _ => ContinuousLinearMap.id ℂ Wq, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
  have hFd := inCC_fpm_id p p₀ hfA
  have hFck := ckOn_fpm p p₀ hf hid
  have hTN : ∀ ε : ℝ, 0 < ε → LimTopN p nn
      (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) :=
    hc₃ Wp Wq P p nn χ _ _ hth1 hχ hFd hFck
  have hZN : ∀ ε : ℝ, 0 < ε → LimZeroN p nn
      (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) Y N :=
    fun ε hε => hCc Wp Wq P p _ χ ε _ N nn Y hCb hχ hε hFck hFd hth2
  exact hC₄ Wp Wq P p f _ _ _ _ b Λ κ₀ 0 p₀ χ nn Y K N Cb hb hΛ hΛb hκ hκb hT (Nat.zero_le _) hp₀ hK hKN hχ hnn
    hCb hf hid hid (amaps_id p f b) hexp hWG hLG hI5 hI5 hTN hTN hZN hZN hE hE hB hB

end
end Formalism.FourierDecayAlt.P.CutBP

namespace Formalism.FourierDecayAlt.P.CutBP
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants
noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem _root_.Formalism.FourierDecayAlt.P.CutBP.thmBpAt_main1Cpt (hA : P5.ThmPActualCpt) (Cb C₃ CΛ C₀ : ℝ) (hC₃ : 0 ≤ C₃) (hCΛ : 0 ≤ CΛ) (hC₀ : 1 / 2 ≤ C₀) :
    ∃ C₄ c₃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
      (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b Λ A₀ : ℝ) (p₀ : ℕ) (χ nn : ℝ → ℝ) (Y : Finset ℝ) (K N : ℕ),
      3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → 1 ≤ TBB.Tq p →
      (p₀ : ℝ) ≤ C₀ * (3 * ((P.r : ℝ) + 1)) + 1 →
      3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nn y) →
      KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) →
      c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      BigCellDerivativeExpansion p f b C₃ (2 * p₀ + 0) →
      TBBx5.WaveGrid p nn Y Λ K N → TBBx5.LiftGrid p nn Y Λ K N →
      (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound p nn
        (apx (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) n) Y K N) →
      LimE p nn χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) Y N →
      TBB.ThmBpAt p f b C₄ 0 p₀ := by
  obtain ⟨C₄, c₃, Cc, h⟩ := thmBpAt_mainCpt hA Cb C₃ CΛ C₀ 0 hC₃ hCΛ hC₀
  refine ⟨C₄, c₃, Cc, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f b Λ A₀ p₀ χ nn Y K N h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 hE
  exact h Wp Wq P p f b Λ 1 A₀ p₀ χ nn Y K N h1 h2 h3 one_pos (by simp) h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 hE (lemB_one p _)

end
end Formalism.FourierDecayAlt.P.CutBP

namespace Formalism.FourierDecayAlt.P.CutBP
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology
noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem _root_.Formalism.FourierDecayAlt.P.CutBP.thmBpAt_main2Cpt (hA : P5.ThmPActualCpt) (Cb C₃ CΛ C₀ : ℝ) (hC₃ : 0 ≤ C₃) (hCΛ : 0 ≤ CΛ) (hC₀ : 1 / 2 ≤ C₀) :
    ∃ C₄ c₃ Cc Cc' : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
      (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b Λ A₀ : ℝ) (p₀ : ℕ) (χ nn : ℝ → ℝ) (Y : Finset ℝ) (K N : ℕ),
      3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → 1 ≤ TBB.Tq p →
      (p₀ : ℝ) ≤ C₀ * (3 * ((P.r : ℝ) + 1)) + 1 →
      3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nn y) →
      KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) →
      c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      Cc' * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      BigCellDerivativeExpansion p f b C₃ (2 * p₀ + 0) →
      TBBx5.WaveGrid p nn Y Λ K N → TBBx5.LiftGrid p nn Y Λ K N →
      (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound p nn
        (apx (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) n) Y K N) →
      LimEvT p χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) Y N →
      LimBd p nn (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) Y N →
      TBB.ThmBpAt p f b C₄ 0 p₀ := by
  obtain ⟨C₄, c₃, Cc, h⟩ := thmBpAt_main1Cpt hA Cb C₃ CΛ C₀ hC₃ hCΛ hC₀
  obtain ⟨Cc', hL⟩ := limE_of_limEvTCpt hA Cb
  refine ⟨C₄, c₃, Cc, Cc', ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f b Λ A₀ p₀ χ nn Y K N h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
    h16 h17 h18 h19 hEv hBd
  have hid : B.CkOn ⊤ (B.GV P.k P.r) (fun _ : B.Mat P.k P.r => ContinuousLinearMap.id ℂ Wq) :=
    fun _ _ => ⟨Set.univ, fun _ => ContinuousLinearMap.id ℂ Wq, isOpen_univ, Set.mem_univ _,
      contDiffOn_const, fun _ _ _ => rfl⟩
  exact h Wp Wq P p f b Λ A₀ p₀ χ nn Y K N h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h16 h17 h18 h19
    (hL Wp Wq P p (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) χ nn
      (A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ)) N Y h10 h8 (fun y => (h9 y).le) (ckOn_fpm p p₀ h11 hid)
      (inCC_fpm_id p p₀ h12) h15 hEv hBd)

end
end Formalism.FourierDecayAlt.P.CutBP

namespace Formalism.FourierDecayAlt.P.CutBP.GT
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical

end
end Formalism.FourierDecayAlt.P.CutBP.GT

namespace Formalism.FourierDecayAlt.P.CutBP
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
noncomputable section

theorem _root_.Formalism.FourierDecayAlt.P.CutBP.limEvT_fpm_of_NFCpt (hA : P5.ThmPActualCpt) (h1 : NFTopFormAllCpt) (h2 : NFTopPtwAll) (h3 : NFTopDomAll) (h4 : NFTopIdAll) (Cb : ℝ) :
    ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
      (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ),
      NFHyp Cb Cc p f A₀ p₀ χ N →
      LimEvT p χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) Y N := by
  obtain ⟨C1, k1⟩ := h1 hA Cb
  obtain ⟨C2, k2⟩ := h2 Cb
  obtain ⟨C3, k3⟩ := h3 Cb
  obtain ⟨C4, k4⟩ := h4 Cb
  refine ⟨max (max C1 C2) (max C3 C4), ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH
  have mono : ∀ C, C ≤ max (max C1 C2) (max C3 C4) → NFHyp Cb C p f A₀ p₀ χ N := by
    intro C hC
    unfold NFHyp at hH ⊢
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hH
    refine ⟨a1, a2, a3, a4, le_trans ?_ a5, a6⟩
    gcongr
  exact limEvT_of_NF p χ _ Y N (k1 Wp Wq P p f A₀ p₀ χ Y N (mono C1 (by simp))) (k2 Wp Wq P p f A₀ p₀ χ Y N (mono C2 (by simp)))
    (k3 Wp Wq P p f A₀ p₀ χ Y N (mono C3 (by simp))) (k4 Wp Wq P p f A₀ p₀ χ Y N (mono C4 (by simp)))

end
end Formalism.FourierDecayAlt.P.CutBP

namespace Formalism.FourierDecayAlt.P.CutBP
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem _root_.Formalism.FourierDecayAlt.P.CutBP.thmBpAt_main4Cpt (hA : P5.ThmPActualCpt) (h1 : NFTopFormAllCpt) (h2 : NFTopPtwAll) (h3 : NFTopDomAll)
    (h4 : NFTopIdAll) (Cb C₃ CΛ C₀ : ℝ) (hC₃ : 0 ≤ C₃) (hCΛ : 0 ≤ CΛ) (hC₀ : 1 / 2 ≤ C₀) :
    ∃ C₄ c₃ Cc Cc' Cc'' : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
      (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b Λ A₀ : ℝ) (p₀ : ℕ) (χ nn : ℝ → ℝ) (Y : Finset ℝ) (K N : ℕ),
      3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → 1 ≤ TBB.Tq p →
      (p₀ : ℝ) ≤ C₀ * (3 * ((P.r : ℝ) + 1)) + 1 →
      3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nn y) →
      KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) →
      c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      Cc' * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      Cc'' * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      N ≤ 2 * p₀ →
      BigCellDerivativeExpansion p f b C₃ (2 * p₀ + 0) →
      TBBx5.WaveGrid p nn Y Λ K N → TBBx5.LiftGrid p nn Y Λ K N →
      (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound p nn
        (apx (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) n) Y K N) →
      LimBd p nn (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) Y N →
      TBB.ThmBpAt p f b C₄ 0 p₀ := by
  obtain ⟨C₄, c₃, Cc, Cc', h⟩ := thmBpAt_main2Cpt hA Cb C₃ CΛ C₀ hC₃ hCΛ hC₀
  obtain ⟨Cn, hn⟩ := limEvT_fpm_of_NFCpt hA h1 h2 h3 h4 Cb
  refine ⟨C₄, c₃, Cc, Cc', Cn, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f b Λ A₀ p₀ χ nn Y K N hb hΛ hΛb hT hp₀ hK hKN hχ hnn hCb hf hfA hth1 hth2 hth3
    hth4 hN2 hexp hWG hLG hI5 hBd
  exact h Wp Wq P p f b Λ A₀ p₀ χ nn Y K N hb hΛ hΛb hT hp₀ hK hKN hχ hnn hCb hf hfA hth1 hth2 hth3 hexp hWG hLG
    hI5 (hn Wp Wq P p f A₀ p₀ χ Y N ⟨hχ, hCb, hf, hfA, hth4, hN2⟩) hBd

end
end Formalism.FourierDecayAlt.P.CutBP

namespace Formalism.FourierDecayAlt.P.CutBP
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical

open GLG in

end
end Formalism.FourierDecayAlt.P.CutBP

namespace Formalism.FourierDecayAlt.P.CutBP
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical

end
end Formalism.FourierDecayAlt.P.CutBP

namespace Formalism.FourierDecayAlt.P.CutBP
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
noncomputable section

end
end Formalism.FourierDecayAlt.P.CutBP

namespace Formalism.FourierDecayAlt.P.CutBP.GT
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical

end
end Formalism.FourierDecayAlt.P.CutBP.GT

namespace Formalism.FourierDecayAlt.P.CutBP
open Formalism.FourierDecayAlt

open Formalism.QuantumDeterminants MeasureTheory in
theorem block_growth_bound_of_compact_coefCpt (hA : P5.ThmPActualCpt) {Wp Wq : Type}
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
    (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (Y : Finset ℝ) (K N : ℕ) (Cb : ℝ) (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ)
    (hG : KB.CptCoef p.T.base G) (hnn : ∀ y, 0 < nn y) : TBB.BlockGrowthBound p nn G Y K N :=
  GlobalTheory.LatticeGerm.latticeSum_of_cptCoef hA _ _ _ p nn G Y K N Cb hCb hG hnn

end Formalism.FourierDecayAlt.P.CutBP
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutMainCpt =====
