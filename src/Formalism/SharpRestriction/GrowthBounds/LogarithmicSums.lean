module

public import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.Conclusion1OfGainBoundAll
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.NumData
public import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.NotSingularOfCentral
public import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.PartnerCountOfCentral
public import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.MeanNum
public import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.StarNum, Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.StarNumB, Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.StarFam, Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.RemainingCountingStatement, Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.GainBoundAllAddOneOfGainBoundAllRequired, Formalism.SharpRestriction.GrowthBounds.LogarithmicSums

-- ===== clump member: Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.StarNum =====
-- clump-header: {"m": "Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.StarNum", "h": "module\n\nimport Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.MeanNum\npublic import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.PartnerCountOfCentral\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G Filter

namespace Formalism.MainNotions.AuxBlock8.Pf.St

def CStar (eps : ℝ) (K : Consts) (C31 : ℝ) : ℝ :=
  3 + K.tII * (rE eps : ℝ) + (2 * (3 : ℝ) + 4 * K.tII + 160 * C31 + 7) + K.Pr1 * C31 + K.kappaThresholdOne * |cNE eps|

def SmallB (D : D7) (L : SizeData₂ D) (K : Consts) (C31 bo : ℝ) : Prop :=
  (∀ p : ℕ, p.Prime → (p : ℝ) < L.sc.p0 D.R.k → (D.R.k : ℝ) * Qp L.sc p ≤ L.sc.b') ∧
  (∀ p : ℕ, p.Prime →
    K.DII * ((N1 L.sc : ℝ) ^ 3 + (rG L.sc : ℝ) ^ 5 + (D.R.k : ℝ) ^ 2) * Real.logb p L.sc.a ≤ L.sc.b') ∧
  (∀ p : ℕ, p.Prime → L.sc.p0 D.R.k ≤ (p : ℝ) → (p : ℝ) < L.sc.X' → ∀ n' : ℕ, n' ≤ D.R.n →
    K.Pr1 * (C31 * Real.log L.sc.x / L.sc.delta1) * (L.etaSz + cG L + Nm D) +
      K.kappaThresholdTwo * (Qp L.sc p * c6f K L p n' +
        (D.R.k : ℝ) * Qp L.sc p + (D.R.k : ℝ) * Real.logb p L.sc.a + cG L) +
      2 * (C31 * Real.log L.sc.x / L.sc.delta1) * cG L +
      40 * C31 * Real.log L.sc.x * (K.DI * (L.sc.x ^ (Scale.A / 2)) ^ 2 *
        ((N1 L.sc : ℝ) ^ 5 + (D.R.k : ℝ) ^ 3) * Real.logb p L.sc.a) + 3 ≤ bo)

theorem numStar_ev (eps : ℝ) (K : Consts) (hK : K.Nonneg) (C31 : ℝ) (hC31 : 0 < C31) :
    ∀ᶠ x : ℝ in atTop, ∀ (D : D7) (L : SizeData₂ D), L.sc.x = x → L.sc.eps = eps → Formalism.MainNotions.SizesAt L →
      ParameterChoice' D L → ∀ bo : ℝ, SmallB D L K C31 bo → ∀ C : ℝ, CStar eps K C31 ≤ C → NumStar D L K C31 C bo := by
  by_cases heps : 0 < eps ∧ eps < 1 / 52
  swap
  · exact Filter.Eventually.of_forall fun x D L _ hLe =>
      absurd ⟨hLe ▸ L.sc.eps_pos, hLe ▸ L.sc.eps_lt⟩ heps
  obtain ⟨he0, he1⟩ := heps
  have E1 : ∀ᶠ x : ℝ in atTop, Real.exp 1 ≤ x := eventually_ge_atTop _
  have E2 := ev_log 514 (eps / 8) (by linarith)
  have E3 := ev_log (3 * cGE eps) (eps / 8) (by linarith)
  have E4 := ev_log (4 * C31) (1 - eps / 8) (by linarith)
  have E5 : ∀ᶠ x : ℝ in atTop, (2 : ℝ) ≤ x := eventually_ge_atTop _
  filter_upwards [E1, E2, E3, E4, E5] with x h1 h2 h3 h4 h5
  intro D L hx hLe hS P bo hSB C hC
  subst hx
  subst hLe
  have hx0 : 0 < L.sc.x := sc_x_pos L.sc
  have hL : 1 ≤ Real.log L.sc.x := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) h1
  have hy0 : 0 ≤ L.sc.x ^ (L.sc.eps / 8) := (Real.rpow_pos_of_pos hx0 _).le
  have hGp := Gp_le L.sc h1
  have hN1 := first_count_le_log L.sc h1
  obtain ⟨-, -, -, htII, -, -, -, -, htI1, -, -, -, -, hPr1, -⟩ := hK
  have hCS : CStar L.sc.eps K C31 ≤ C := hC
  unfold CStar at hCS
  have ha := mul_nonneg htII (Nat.cast_nonneg (α := ℝ) (rE L.sc.eps))
  have hb := mul_nonneg hPr1 hC31.le
  have hc := mul_nonneg htI1 (abs_nonneg (cNE L.sc.eps))
  obtain ⟨hw500, hcGw, hwb, hcG0, hScG⟩ := base P
  obtain ⟨-, hNmSc, -⟩ := Nm_le_Sc P
  have hn1 : 1 ≤ D.R.n := by
    have hexp : 0 ≤ 2 + 8 * L.sc.eps - Formalism.MainNotions.szTh L := by
      unfold Formalism.MainNotions.szTh
      linarith
    have h1n : (1 : ℝ) ≤ D.R.n := le_trans (Real.one_le_rpow L.sc.one_lt_alt.le hexp) hS.1.1
    exact_mod_cast h1n
  obtain ⟨hwx, -⟩ := w''_le L.sc D.R.n hn1
  have hb0 : 0 ≤ L.sc.b' := by linarith
  have hbx : L.sc.b' / L.sc.x ≤ L.sc.b' / 2 := div_le_div_of_nonneg_left hb0 (by norm_num) h5
  have hEta := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ht1 : (1 : ℝ) ≤ D.R.t := by exact_mod_cast D.R.t_odd.pos
  have heta0 : 0 ≤ L.etaSz := by linarith [hEta.1]
  have heta : L.etaSz ≤ L.sc.w'' D.R.n := by
    have h4e := hEta.2.2.2.1
    have hwx' : L.sc.w'' D.R.n / L.sc.x ≤ L.sc.w'' D.R.n :=
      div_le_self (by linarith) L.sc.one_lt_alt.le
    nlinarith
  have hNm : Nm D ≤ L.sc.w'' D.R.n := by
    unfold Nm
    linarith
  have hS4 : L.sc.w'' D.R.n + L.etaSz + cG L + Nm D ≤ 4 * (L.sc.b' / L.sc.x) := by linarith
  have hkey : 4 * C31 * Real.log L.sc.x * L.sc.x ^ (L.sc.eps / 8) ≤ L.sc.x := by
    calc 4 * C31 * Real.log L.sc.x * L.sc.x ^ (L.sc.eps / 8)
        ≤ L.sc.x ^ (1 - L.sc.eps / 8) * L.sc.x ^ (L.sc.eps / 8) :=
          mul_le_mul_of_nonneg_right h4 hy0
      _ = L.sc.x := by rw [← Real.rpow_add hx0]; simp
  have hinv := inv_delta1 L.sc
  have hrG : (rG L.sc : ℝ) = (rE L.sc.eps : ℝ) := rfl
  exact
    { hL2 := second_level_lt_good_of_log L hS h1 h2
      h3G := by
        push_cast
        calc (3 : ℝ) * (Gp L.sc : ℝ) ≤ 3 * (cGE L.sc.eps * Real.log L.sc.x * L.sc.x ^ (L.sc.eps / 8)) := by
              linarith
          _ = (3 * cGE L.sc.eps * Real.log L.sc.x) * L.sc.x ^ (L.sc.eps / 8) := by ring
          _ ≤ L.sc.x ^ (L.sc.eps / 8) * L.sc.x ^ (L.sc.eps / 8) := mul_le_mul_of_nonneg_right h3 hy0
          _ = L.sc.x ^ (L.sc.eps / 4) := by rw [← Real.rpow_add hx0]; ring_nf
      hlx := hL
      hGu := by
        have hpos : 0 ≤ C31 * Real.log L.sc.x * L.sc.x ^ (L.sc.eps / 8) :=
          mul_nonneg (mul_nonneg hC31.le (by linarith)) hy0
        calc C31 * Real.log L.sc.x / L.sc.delta1 * (L.sc.w'' D.R.n + L.etaSz + cG L + Nm D)
            = (C31 * Real.log L.sc.x * (1 / L.sc.delta1)) *
                (L.sc.w'' D.R.n + L.etaSz + cG L + Nm D) := by ring
          _ = (C31 * Real.log L.sc.x * L.sc.x ^ (L.sc.eps / 8)) *
                (L.sc.w'' D.R.n + L.etaSz + cG L + Nm D) := by rw [hinv]
          _ ≤ (C31 * Real.log L.sc.x * L.sc.x ^ (L.sc.eps / 8)) * (4 * (L.sc.b' / L.sc.x)) :=
              mul_le_mul_of_nonneg_left hS4 hpos
          _ = (4 * C31 * Real.log L.sc.x * L.sc.x ^ (L.sc.eps / 8)) * L.sc.b' / L.sc.x := by ring
          _ ≤ L.sc.x * L.sc.b' / L.sc.x := by gcongr
          _ = L.sc.b' := by field_simp
      hc0 := by
        unfold c0num
        linarith
      hkQ := hSB.1
      hDII := hSB.2.1
      hC3 := by linarith
      hCt := by rw [hrG]; linarith
      hCD := by linarith
      hCP := by linarith
      hN1 := by
        have hN1' : (N1 L.sc : ℝ) ≤ |cNE L.sc.eps| * Real.log L.sc.x :=
          hN1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith))
        calc K.kappaThresholdOne * (N1 L.sc : ℝ) ≤ K.kappaThresholdOne * (|cNE L.sc.eps| * Real.log L.sc.x) :=
              mul_le_mul_of_nonneg_left hN1' htI1
          _ = (K.kappaThresholdOne * |cNE L.sc.eps|) * Real.log L.sc.x := by ring
          _ ≤ C * Real.log L.sc.x := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      hbo := hSB.2.2 }

end Formalism.MainNotions.AuxBlock8.Pf.St

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.StarNum =====

-- ===== clump member: Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.StarNumB =====
-- clump-header: {"m": "Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.StarNumB", "h": "module\n\npublic import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.NumData\npublic import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes\npublic import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.Conclusion1OfGainBoundAll\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G Filter
open Formalism.MainNotions.AuxBlock8.Pf.G5.Nu

namespace Formalism.MainNotions.AuxBlock8.Pf.St.B

theorem hboB_arith (Y Pr1 G η c Nm kappaThresholdTwo Q DIf N k lb n' C31 lx DI v N1 Np : ℝ) (hY : 130 ≤ Y)
    (b1 : Pr1 ≤ Y) (a2 : 0 ≤ G) (b2 : G ≤ Y) (a3 : 0 ≤ η) (b3 : η ≤ Y) (a4 : 0 ≤ c) (b4 : c ≤ Y)
    (a5 : 0 ≤ Nm) (b5 : Nm ≤ Y) (a6 : 0 ≤ kappaThresholdTwo) (b6 : kappaThresholdTwo ≤ Y) (a7 : 0 ≤ Q) (b7 : Q ≤ Y) (a8 : 0 ≤ DI) (b8 : DI ≤ Y)
    (a9 : 0 ≤ N) (b9 : N ≤ Y) (a10 : 0 ≤ k) (b10 : k ≤ Y) (a11 : 0 ≤ lb) (b11 : lb ≤ Y) (a12 : 0 ≤ n') (b12 : n' ≤ Y)
    (b13 : C31 ≤ Y) (a14 : 0 ≤ lx) (b14 : lx ≤ Y) (a15 : 0 ≤ v) (b15 : v ≤ Y) (a16 : 0 ≤ N1)
    (b16 : N1 ≤ Y) (a17 : 0 ≤ Np) (b17 : Np ≤ Y) (a18 : 0 ≤ DIf)
    (hD : DIf ≤ DI * Np * v ^ 2 * (N1 ^ 5 + k ^ 3) * lb + 1) :
    Pr1 * G * (η + c + Nm) + kappaThresholdTwo * (Q * (8 * (DIf + 1) + kappaThresholdTwo * N * k * lb + 4 * N * c + 2 * n' * c) + k * Q +
      k * lb + c) + 2 * G * c + 40 * C31 * lx * (DI * v ^ 2 * (N1 ^ 5 + k ^ 3) * lb) + 3 ≤ Y ^ 13 := by
  have hY1 : 1 ≤ Y := by linarith
  have hD' : DIf ≤ Y * Y * Y ^ 2 * (Y ^ 5 + Y ^ 3) * Y + 1 := le_trans hD (by gcongr)
  have h1 : Pr1 * G * (η + c + Nm) + kappaThresholdTwo * (Q * (8 * (DIf + 1) + kappaThresholdTwo * N * k * lb + 4 * N * c + 2 * n' * c) + k * Q +
      k * lb + c) + 2 * G * c + 40 * C31 * lx * (DI * v ^ 2 * (N1 ^ 5 + k ^ 3) * lb) + 3 ≤
      Y * Y * (Y + Y + Y) + Y * (Y * (8 * ((Y * Y * Y ^ 2 * (Y ^ 5 + Y ^ 3) * Y + 1) + 1) + Y * Y * Y * Y + 4 * Y * Y +
        2 * Y * Y) + Y * Y + Y * Y + Y) + 2 * Y * Y + 40 * Y * Y * (Y * Y ^ 2 * (Y ^ 5 + Y ^ 3) * Y) + 3 := by gcongr
  have p : ∀ i : ℕ, i ≤ 12 → Y ^ i ≤ Y ^ 12 := fun i hi => pow_le_pow_right₀ hY1 hi
  have p11 := p 11 (by norm_num)
  have p10 := p 10 (by norm_num)
  have p9 := p 9 (by norm_num)
  have p6 := p 6 (by norm_num)
  have p4 := p 4 (by norm_num)
  have p3 := p 3 (by norm_num)
  have p2 := p 2 (by norm_num)
  have p0 : 1 ≤ Y ^ 12 := one_le_pow₀ hY1
  have p13 : 130 * Y ^ 12 ≤ Y ^ 13 := by
    calc 130 * Y ^ 12 ≤ Y * Y ^ 12 := mul_le_mul_of_nonneg_right hY (by positivity)
      _ = Y ^ 13 := by ring
  linarith

theorem hDII_arith (Y DII N1 r k lb : ℝ) (hY : 130 ≤ Y) (b1 : DII ≤ Y) (a2 : 0 ≤ N1) (b2 : N1 ≤ Y)
    (a3 : 0 ≤ r) (b3 : r ≤ Y) (a4 : 0 ≤ k) (b4 : k ≤ Y) (a5 : 0 ≤ lb) (b5 : lb ≤ Y) :
    DII * (N1 ^ 3 + r ^ 5 + k ^ 2) * lb ≤ Y ^ 8 := by
  have hY1 : 1 ≤ Y := by linarith
  have h1 : DII * (N1 ^ 3 + r ^ 5 + k ^ 2) * lb ≤ Y * (Y ^ 3 + Y ^ 5 + Y ^ 2) * Y := by gcongr
  have p5 : Y ^ 5 ≤ Y ^ 7 := pow_le_pow_right₀ hY1 (by norm_num)
  have p4 : Y ^ 4 ≤ Y ^ 7 := pow_le_pow_right₀ hY1 (by norm_num)
  have p8 : 130 * Y ^ 7 ≤ Y ^ 8 := by
    calc 130 * Y ^ 7 ≤ Y * Y ^ 7 := mul_le_mul_of_nonneg_right hY (by positivity)
      _ = Y ^ 8 := by ring
  have : 0 ≤ Y ^ 7 := by positivity
  linarith

structure Facts (D : D7) (L : SizeData₂ D) (K : Consts) (C31 bo : ℝ) : Prop where
  hkQ : ∀ p : ℕ, p.Prime → (p : ℝ) < L.sc.p0 D.R.k → (D.R.k : ℝ) * Qp L.sc p ≤ L.sc.b'
  hDII : ∀ p : ℕ, p.Prime →
    K.DII * ((N1 L.sc : ℝ) ^ 3 + (rG L.sc : ℝ) ^ 5 + (D.R.k : ℝ) ^ 2) * Real.logb p L.sc.a ≤ L.sc.b'
  hbo : ∀ p : ℕ, p.Prime → L.sc.p0 D.R.k ≤ (p : ℝ) → (p : ℝ) < L.sc.X' → ∀ n' : ℕ, n' ≤ D.R.n →
    K.Pr1 * (C31 * Real.log L.sc.x / L.sc.delta1) * (L.etaSz + cG L + Nm D) +
      K.kappaThresholdTwo * (Qp L.sc p * c6f K L p n' +
        (D.R.k : ℝ) * Qp L.sc p + (D.R.k : ℝ) * Real.logb p L.sc.a + cG L) +
      2 * (C31 * Real.log L.sc.x / L.sc.delta1) * cG L +
      40 * C31 * Real.log L.sc.x * (K.DI * (L.sc.x ^ (Scale.A / 2)) ^ 2 *
        ((N1 L.sc : ℝ) ^ 5 + (D.R.k : ℝ) ^ 3) * Real.logb p L.sc.a) + 3 ≤ bo


theorem facts_ev (eps : ℝ) (K : Consts) (hK : K.Nonneg) (C31 : ℝ) (hC31 : 0 < C31) :
    ∀ᶠ x : ℝ in atTop, ∀ (D : D7) (L : SizeData₂ D), L.sc.x = x → L.sc.eps = eps → Formalism.MainNotions.SizesAt L →
      ParameterChoice' D L → adm5 D L K (eps / 48) → Facts D L K C31 (L.sc.b ^ (x ^ (-(eps / 2)))) := by
  by_cases he : 0 < eps ∧ eps < 1 / 52
  swap
  · refine Filter.Eventually.of_forall fun x D L _ h2 => ?_
    exact absurd ⟨h2 ▸ L.sc.eps_pos, h2 ▸ L.sc.eps_lt⟩ he
  obtain ⟨he0, he1⟩ := he
  have hτ : 0 < 23 * eps / 48 := by positivity
  have F1 := ev_log 14 (23 * eps / 48) hτ
  have F2 := ev_const 130 (23 * eps / 48) hτ
  have G1 := ev_const K.Pr1 (23 * eps / 48) hτ
  have G2 := ev_const K.kappaThresholdTwo (23 * eps / 48) hτ
  have G3 := ev_const K.DI (23 * eps / 48) hτ
  have G4 := ev_const K.DII (23 * eps / 48) hτ
  have G5 := ev_const C31 (23 * eps / 48) hτ
  have G6 := ev_const (rE eps : ℝ) (23 * eps / 48) hτ
  have F4 := ev_log 1 eps he0
  have F5 := ev_pow 3 eps 1 (by linarith)
  have F6 := ev_pow 14 (23 * eps / 48) eps (by linarith)
  have F7 := ev_pow 4 (eps / 3) eps (by linarith)
  have F8 := ev_pow 13 (23 * eps / 48) (eps / 2) (by linarith)
  have F9 := ev_log C31 1 one_pos
  have WorkedExample := ev_log (cNE eps) 1 one_pos
  filter_upwards [F1, F2, G1, G2, G3, G4, G5, G6, F4, F5, F6, F7, F8, F9, WorkedExample, eventually_ge_atTop 40,
    eventually_ge_atTop (Real.exp 1)] with x f1 f2 g1 g2 g3 g4 g5 g6 f4 f5 f6 f7 f8 f9 f10 hx40 hxe D L hx heps hS P h5
  subst hx
  subst heps
  obtain ⟨_, _, _, _, _, _, _, hDI0, _, htI20, _, _, _, _, _⟩ := hK
  have hx0 := sc_x_pos L.sc
  have hx1 := L.sc.one_lt_alt
  have hlx0 : 0 ≤ Real.log L.sc.x := Real.log_nonneg hx1.le
  have hk1 := one_le_k D
  have hk6 := k_le_x_pow_six L hS
  have hk0 : (0 : ℝ) < (D.R.k : ℝ) := by linarith
  obtain ⟨_, hNmSc, hSc100⟩ := Nm_le_Sc P
  obtain ⟨hSN, -, -, -, -, -, -, -, -, -, -, -, -, hSEta, -, -, hSDel, -⟩ := hS
  unfold Formalism.MainNotions.SizeN Formalism.MainNotions.szTh at hSN
  unfold Formalism.MainNotions.SizeEta at hSEta
  unfold Formalism.MainNotions.SizeDel at hSDel
  rw [Real.rpow_one] at f5 f9 f10
  have mono : ∀ u v : ℝ, u ≤ v → L.sc.x ^ u ≤ L.sc.x ^ v := fun u v h => Real.rpow_le_rpow_of_exponent_le hx1.le h
  have nat3 : L.sc.x ^ (3 : ℝ) = L.sc.x ^ 3 := by rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have nat6 : L.sc.x ^ (6 : ℝ) = L.sc.x ^ 6 := by rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have natA2 : L.sc.x ^ (Scale.A / 2) = L.sc.x ^ 13 := by
    unfold Scale.A; rw [show (26 / 2 : ℝ) = ((13 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hn3 : (D.R.n : ℝ) ≤ L.sc.x ^ 3 := by rw [← nat3]; exact le_trans hSN.2 (mono _ _ (by linarith))
  rw [nat6] at hk6
  have hb : L.sc.b = Real.exp (L.sc.x ^ L.sc.eps) := rfl
  have ha : L.sc.a = L.sc.x * L.sc.b := rfl
  have hY130 : 130 ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := f2
  have hY0 : 0 < (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := Real.exp_pos _
  have pY : ∀ q : ℝ, ∀ M : ℕ, q ≤ L.sc.x ^ M → M ≤ 14 → q ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := by
    intro q M hq hM
    refine le_trans hq ?_
    rw [← Real.rpow_natCast]
    apply xpow_le_exp _ _ _ hx0
    have : (M : ℝ) ≤ 14 := by exact_mod_cast hM
    exact le_trans (mul_le_mul_of_nonneg_right this hlx0) f1
  have e_eta : L.etaSz ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) :=
    calc L.etaSz ≤ Real.exp (Real.log L.etaSz) := Real.le_exp_log _
      _ ≤ Real.exp (L.sc.x ^ (L.sc.eps / 4)) := Real.exp_le_exp.2 hSEta.2.2.1
      _ ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := Real.exp_le_exp.2 (mono _ _ (by linarith))
  have hT4 : L.sc.x ^ (L.sc.eps / 4) ≤ (L.sc.x ^ (23 * L.sc.eps / 48)) := mono _ _ (by linarith)
  have e_Del : (D.s.Del : ℝ) ≤ Real.exp ((L.sc.x ^ (23 * L.sc.eps / 48)) / 2) :=
    calc (D.s.Del : ℝ) ≤ Real.exp (Real.log (D.s.Del : ℝ)) := Real.le_exp_log _
      _ ≤ Real.exp (L.sc.x ^ (L.sc.eps / 4) / 2) := Real.exp_le_exp.2 hSDel.2.2.1
      _ ≤ _ := Real.exp_le_exp.2 (by linarith)
  have hDel0 : (0 : ℝ) ≤ (D.s.Del : ℝ) := by
    have h := L.Sc_eq
    by_contra hneg
    have : (D.R.k : ℝ) * (4 * (D.s.Del : ℝ)) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hk0.le (by linarith)
    linarith
  have h7 : L.sc.x * L.sc.x ^ 6 ≤ Real.exp ((L.sc.x ^ (23 * L.sc.eps / 48)) / 2) := by
    have : L.sc.x * L.sc.x ^ 6 = L.sc.x ^ ((7 : ℕ) : ℝ) := by rw [Real.rpow_natCast]; ring
    rw [this]
    apply xpow_le_exp _ _ _ hx0
    push_cast
    linarith
  have hcG0 : 0 ≤ cG L := by unfold cG; linarith
  have e_c : cG L ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) :=
    calc cG L = (16 * (D.R.k : ℝ)) * (D.s.Del : ℝ) := by unfold cG; rw [L.Sc_eq]; ring
      _ ≤ (L.sc.x * L.sc.x ^ 6) * Real.exp ((L.sc.x ^ (23 * L.sc.eps / 48)) / 2) :=
          mul_le_mul (mul_le_mul (by linarith) hk6 hk0.le hx0.le) e_Del hDel0 (by positivity)
      _ ≤ Real.exp ((L.sc.x ^ (23 * L.sc.eps / 48)) / 2) * Real.exp ((L.sc.x ^ (23 * L.sc.eps / 48)) / 2) := mul_le_mul_of_nonneg_right h7 (Real.exp_pos _).le
      _ = (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := by rw [← Real.exp_add]; congr 1; ring
  have e_Nm : Nm D ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := by
    have : Nm D ≤ cG L := by unfold Nm cG; linarith
    linarith
  have hNm0 : 0 ≤ Nm D := by unfold Nm; exact Nat.cast_nonneg _
  have e_n : (D.R.n : ℝ) ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := pY _ 3 hn3 (by norm_num)
  have e_k : (D.R.k : ℝ) ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := pY _ 6 hk6 (by norm_num)
  have e_v : L.sc.x ^ (Scale.A / 2) ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := pY _ 13 (le_of_eq natA2) (by norm_num)
  have hxY : L.sc.x ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := pY _ 1 (by rw [pow_one]) (by norm_num)
  have e_lx : Real.log L.sc.x ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := by linarith
  have hla : Real.log L.sc.a = Real.log L.sc.x + L.sc.x ^ L.sc.eps := by
    rw [ha, hb, Real.log_mul hx0.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hla0 : 0 ≤ Real.log L.sc.a := by rw [hla]; positivity
  have hlaX : 2 * Real.log L.sc.a ≤ L.sc.x ^ 2 := by
    rw [hla]
    have : 2 * L.sc.x ≤ L.sc.x ^ 2 := by rw [pow_two]; exact mul_le_mul_of_nonneg_right (by linarith) hx0.le
    linarith
  have e_lb : ∀ p : ℕ, p.Prime → 0 ≤ Real.logb p L.sc.a ∧ Real.logb p L.sc.a ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
    have hlp : (1 / 2 : ℝ) ≤ Real.log p := le_trans hl2 (Real.log_le_log (by norm_num) hp2)
    unfold Real.logb
    refine ⟨div_nonneg hla0 (by linarith), ?_⟩
    refine pY _ 2 (le_trans ?_ hlaX) (by norm_num)
    rw [div_le_iff₀ (by linarith)]
    calc Real.log L.sc.a = 2 * Real.log L.sc.a * (1 / 2) := by ring
      _ ≤ 2 * Real.log L.sc.a * Real.log p := mul_le_mul_of_nonneg_left hlp (by linarith)
  have hd : 1 / L.sc.delta1 = L.sc.x ^ (L.sc.eps / 8) := inv_delta1 L.sc
  have h8 : L.sc.x ^ (L.sc.eps / 8) ≤ L.sc.x := by
    have := mono (L.sc.eps / 8) 1 (by linarith)
    rwa [Real.rpow_one] at this
  have h80 : 0 ≤ L.sc.x ^ (L.sc.eps / 8) := Real.rpow_nonneg hx0.le _
  have hG0 : 0 ≤ C31 * Real.log L.sc.x / L.sc.delta1 := div_nonneg (mul_nonneg hC31.le hlx0) (sc_delta1_pos L.sc).le
  have e_G : C31 * Real.log L.sc.x / L.sc.delta1 ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := by
    refine pY _ 2 ?_ (by norm_num)
    calc C31 * Real.log L.sc.x / L.sc.delta1 = C31 * Real.log L.sc.x * (1 / L.sc.delta1) := by ring
      _ = C31 * Real.log L.sc.x * L.sc.x ^ (L.sc.eps / 8) := by rw [hd]
      _ ≤ L.sc.x * L.sc.x := mul_le_mul f9 h8 h80 hx0.le
      _ = L.sc.x ^ 2 := by ring
  have e_N1 : (N1 L.sc : ℝ) ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := le_trans (le_trans (first_count_le_log L.sc hxe) f10) hxY
  have hd1 : L.sc.delta1 ≤ 1 := by
    unfold Scale.delta1
    exact Real.rpow_le_one_of_one_le_of_nonpos hx1.le (by linarith)
  have e_Q : ∀ p : ℕ, p.Prime → (p : ℝ) < L.sc.X' → Qp L.sc p ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := by
    intro p hp hpX
    calc Qp L.sc p ≤ Real.exp (Real.log (Qp L.sc p)) := Real.le_exp_log _
      _ ≤ Real.exp (L.sc.x ^ (11 * L.sc.eps / 24 + L.sc.eps / 48)) := Real.exp_le_exp.2 ((h5.2.2 p hp).2 hpX)
      _ ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := Real.exp_le_exp.2 (mono _ _ (by linarith))
  have e_Q0 : ∀ p : ℕ, p.Prime → (p : ℝ) < L.sc.p0 D.R.k → Qp L.sc p ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := by
    intro p hp hpX
    calc Qp L.sc p ≤ Real.exp (Real.log (Qp L.sc p)) := Real.le_exp_log _
      _ ≤ Real.exp (L.sc.x ^ (L.sc.eps / 8 + L.sc.eps / 48)) := Real.exp_le_exp.2 ((h5.2.2 p hp).1 hpX)
      _ ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := Real.exp_le_exp.2 (mono _ _ (by linarith))
  have hQ0 : ∀ p : ℕ, 0 ≤ Qp L.sc p := fun p => by unfold Qp; positivity
  have e8 : (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) ^ 8 ≤ L.sc.b' := by
    have h2 : L.sc.b' = L.sc.x * Real.exp (L.sc.x ^ L.sc.eps - L.sc.x ^ (L.sc.eps / 3)) := by
      unfold Scale.b' Scale.a Scale.b Scale.X' Scale.L
      rw [Real.exp_sub]; ring
    rw [h2, ← Real.exp_nat_mul]
    calc Real.exp (((8 : ℕ) : ℝ) * (L.sc.x ^ (23 * L.sc.eps / 48))) ≤ Real.exp (L.sc.x ^ L.sc.eps - L.sc.x ^ (L.sc.eps / 3)) := by
          apply Real.exp_le_exp.2
          push_cast
          linarith
      _ = 1 * Real.exp (L.sc.x ^ L.sc.eps - L.sc.x ^ (L.sc.eps / 3)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hx1.le (Real.exp_pos _).le
  refine ⟨?_, ?_, ?_⟩
  · intro p hp hp0
    have h1 : (D.R.k : ℝ) * Qp L.sc p ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) * (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := mul_le_mul e_k (e_Q0 p hp hp0) (hQ0 p) hY0.le
    have h2 : (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) * (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) ^ 8 := by
      rw [← pow_two]; exact pow_le_pow_right₀ (by linarith) (by norm_num)
    linarith
  · intro p hp
    rw [rG_rE]
    exact le_trans (hDII_arith (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) K.DII _ _ _ _ hY130 g4 (Nat.cast_nonneg _) e_N1 (Nat.cast_nonneg _) g6 hk0.le e_k
      (e_lb p hp).1 (e_lb p hp).2) e8
  · intro p hp _ hpX n' hn'
    have hbo : L.sc.b ^ (L.sc.x ^ (-(L.sc.eps / 2))) = Real.exp (L.sc.x ^ (L.sc.eps / 2)) := by
      rw [hb, ← Real.exp_mul, ← Real.rpow_add hx0]
      congr 2
      ring
    rw [hbo]
    have hn'R : (n' : ℝ) ≤ (D.R.n : ℝ) := by exact_mod_cast hn'
    have hNp0 : 0 ≤ NplusF L.sc n' := by
      unfold NplusF; exact mul_nonneg (by positivity) (sc_delta1_pos L.sc).le
    have hNp : NplusF L.sc n' ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := by
      refine pY _ 4 ?_ (by norm_num)
      unfold NplusF
      calc 40 * (n' : ℝ) * L.sc.delta1 ≤ L.sc.x * L.sc.x ^ 3 * 1 :=
            mul_le_mul (mul_le_mul hx40 (le_trans hn'R hn3) (Nat.cast_nonneg _) hx0.le) hd1
              (sc_delta1_pos L.sc).le (by positivity)
        _ = L.sc.x ^ 4 := by ring
    have hval0 : 0 ≤ K.DI * NplusF L.sc n' * (L.sc.x ^ (Scale.A / 2)) ^ 2 * ((N1 L.sc : ℝ) ^ 5 + (D.R.k : ℝ) ^ 3) *
        Real.logb p L.sc.a :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hDI0 hNp0) (by positivity)) (by positivity)) (e_lb p hp).1
    have hDIf : (DIf K L p n' : ℝ) ≤ K.DI * NplusF L.sc n' * (L.sc.x ^ (Scale.A / 2)) ^ 2 *
        ((N1 L.sc : ℝ) ^ 5 + (D.R.k : ℝ) ^ 3) * Real.logb p L.sc.a + 1 := by
      unfold DIf
      exact (Nat.ceil_lt_add_one hval0).le
    have h13 : (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) ^ 13 ≤ Real.exp (L.sc.x ^ (L.sc.eps / 2)) := by
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.2
      push_cast
      exact f8
    refine le_trans ?_ h13
    unfold c6f
    exact hboB_arith (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) K.Pr1 _ L.etaSz (cG L) (Nm D) K.kappaThresholdTwo (Qp L.sc p) _ (NplusF L.sc n') (D.R.k : ℝ) _ (n' : ℝ) C31 _ K.DI _
      (N1 L.sc : ℝ) (NplusF L.sc n') hY130 g1 hG0 e_G L.etaSz_pos.le e_eta hcG0 e_c hNm0 e_Nm htI20 g2 (hQ0 p)
      (e_Q p hp hpX) hDI0 g3 hNp0 hNp hk0.le e_k (e_lb p hp).1 (e_lb p hp).2
      (Nat.cast_nonneg _) (le_trans hn'R e_n) g5 hlx0 e_lx (Real.rpow_nonneg hx0.le _) e_v (Nat.cast_nonneg _) e_N1
      hNp0 hNp (Nat.cast_nonneg _) hDIf

end Formalism.MainNotions.AuxBlock8.Pf.St.B

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.StarNumB =====

-- ===== clump member: Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.StarFam =====
-- clump-header: {"m": "Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.StarFam", "h": "module\n\npublic import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.Conclusion1OfGainBoundAll\npublic import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.StarNum\npublic import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.StarNumB\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\npublic import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.PartnerCountOfCentral\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G Filter

namespace Formalism.MainNotions.AuxBlock8.Pf.St

theorem star_fam {eps : ℝ} (Fm : FamP eps) (K : Consts) (hK : K.Nonneg) (C31 Ce Cm : ℝ) (hC31 : 0 < C31) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ C ≥ C0, ∀ (X : ∀ x (i : Fm.Ix x), Inst (Fm.D x i) (Fm.L x i))
      (Y : ∀ x (i : Fm.Ix x), LatInst (Fm.D x i)), AdmFam Fm K X Y C31 Ce Cm →
      ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, StarAll (X x i) K C ((Fm.L x i).sc.b ^ (x ^ (-(eps / 2)))) := by
  have heps : 0 < eps := by
    obtain ⟨i0⟩ := Fm.Ix_zero
    rw [← Fm.L_eps 0 i0]
    exact (Fm.L 0 i0).sc.eps_pos
  refine ⟨max (CStar eps K C31) 0, le_max_right _ _, fun C hC X Y hAdm => ?_⟩
  obtain ⟨x2, -, hx2⟩ := hAdm (eps / 48) (by linarith)
  obtain ⟨x3, hx3⟩ := Filter.eventually_atTop.1
    ((numStar_ev eps K hK C31 hC31).and (B.facts_ev eps K hK C31 hC31))
  refine ⟨max (max x2 x3) (Fm.x1 + 1), fun x hx i => ?_⟩
  have h1 := le_max_left (max x2 x3) (Fm.x1 + 1)
  have h2 := le_max_right (max x2 x3) (Fm.x1 + 1)
  have h3 := le_max_left x2 x3
  have h4 := le_max_right x2 x3
  have hxx1 : Fm.x1 < x := by linarith
  have hP := Fm.params x hxx1 i
  have hS := Fm.sizes x hxx1 i
  obtain ⟨A1, -, A5, -⟩ := hx2 x (by linarith) i
  have hx3' := hx3 x (by linarith)
  have hF := hx3'.2 (Fm.D x i) (Fm.L x i) (Fm.L_x x i hxx1) (Fm.L_eps x i) hS hP A5
  have hN := hx3'.1 (Fm.D x i) (Fm.L x i) (Fm.L_x x i hxx1) (Fm.L_eps x i) hS hP _
    ⟨hF.hkQ, hF.hDII, hF.hbo⟩ C (le_trans (le_max_left _ _) hC)
  exact starAll_of (X x i) hK hP A1 hC31 hN

end Formalism.MainNotions.AuxBlock8.Pf.St

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.StarFam =====

-- ===== clump member: Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.RemainingCountingStatement =====
-- clump-header: {"m": "Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.RemainingCountingStatement", "h": "module\n\npublic import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.Conclusion1OfGainBoundAll\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G

namespace Formalism.MainNotions.AuxBlock8.Pf

def FamilyAskBounds {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ K : Consts, K.Nonneg → ∀ C31 Ce Cm : ℝ, 0 < C31 → 0 ≤ Ce → 0 ≤ Cm →
    ∀ (X : ∀ x (i : Fm.Ix x), Inst (Fm.D x i) (Fm.L x i)) (Y : ∀ x (i : Fm.Ix x), LatInst (Fm.D x i)),
      AdmFam Fm K X Y C31 Ce Cm → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, RequiresAll (X x i)

def RemainingCountingStatement {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ K : Consts, K.Nonneg → ∀ C31 Ce Cm : ℝ, 0 < C31 → 0 ≤ Ce → 0 ≤ Cm →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : ∀ x (i : Fm.Ix x), Inst (Fm.D x i) (Fm.L x i)) (Y : ∀ x (i : Fm.Ix x), LatInst (Fm.D x i)),
      AdmFam Fm K X Y C31 Ce Cm → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
        GainBoundAll (X x i) K C ((Fm.L x i).sc.b ^ (x ^ (-(eps / 2))))

def FamilyFourthBound {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ K : Consts, K.Nonneg → ∀ C31 Ce Cm : ℝ, 0 < C31 → 0 ≤ Ce → 0 ≤ Cm →
    ∀ (X : ∀ x (i : Fm.Ix x), Inst (Fm.D x i) (Fm.L x i)) (Y : ∀ x (i : Fm.Ix x), LatInst (Fm.D x i)),
      AdmFam Fm K X Y C31 Ce Cm → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Conclusion2 (Fm.D x i) (Fm.L x i) (X x i) K

theorem eps_pos {eps : ℝ} (Fm : FamP eps) : 0 < eps := by
  obtain ⟨i⟩ := Fm.Ix_zero
  rw [← Fm.L_eps 0 i]
  exact (Fm.L 0 i).sc.eps_pos

theorem stmtEF_of {eps : ℝ} (Fm : FamP eps) (h0 : FamilyAskBounds Fm) (h1 : RemainingCountingStatement Fm) (h2 : FamilyFourthBound Fm) :
    FamilyClosedForm Fm := by
  intro K hK C31 Ce Cm hC31 hCe hCm
  obtain ⟨C, hC, hG⟩ := h1 K hK C31 Ce Cm hC31 hCe hCm
  refine ⟨C, hC, fun X Y hA => ?_⟩
  obtain ⟨a0, ha0⟩ := h0 K hK C31 Ce Cm hC31 hCe hCm X Y hA
  obtain ⟨a1, ha1⟩ := hG X Y hA
  obtain ⟨a2, ha2⟩ := h2 K hK C31 Ce Cm hC31 hCe hCm X Y hA
  refine ⟨fun x => x ^ (-(eps / 2)), ?_, max a0 (max a1 a2), fun x hx i => ?_⟩
  · exact tendsto_rpow_neg_atTop (half_pos (eps_pos Fm))
  · simp only [ge_iff_le, max_le_iff] at hx
    obtain ⟨e0, e1, e2⟩ := hx
    have g0 := ha0 x e0 i
    have g1 := ha1 x e1 i
    have g2 := ha2 x e2 i
    have g1' := g1 (aL (Fm.L x i)) (bL (Fm.L x i))
    refine ⟨g1' ?_, g2, fun a b ha hb p hp _ => g0 a b ha hb p hp⟩

    intro t ht
    unfold aL bL
    simp only [dite_eq_left ht]
    exact ⟨((Fm.L x i).aT_win ⟨t, ht⟩).1, ((Fm.L x i).aT_win ⟨t, ht⟩).2, (Fm.L x i).bT_ge ⟨t, ht⟩⟩

theorem stmtF_of_stmtEF {eps : ℝ} (Fm : FamP eps) (h : FamilyClosedForm Fm) : KudlaFamilyStatement Fm := by
  intro K hK X Y hA
  obtain ⟨C31, Ce, Cm, hC31, hCe, hCm, hA'⟩ := hA
  obtain ⟨C, hC, hP⟩ := h K hK C31 Ce Cm hC31 hCe hCm
  exact ⟨C, hP X Y hA'⟩

end Formalism.MainNotions.AuxBlock8.Pf

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.RemainingCountingStatement =====

-- ===== clump member: Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.GainBoundAllAddOneOfGainBoundAllRequired =====
-- clump-header: {"m": "Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.GainBoundAllAddOneOfGainBoundAllRequired", "h": "module\n\npublic import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.Conclusion1OfGainBoundAll\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G

namespace Formalism.MainNotions.AuxBlock8.Pf.As

variable {D : D7} {L : SizeData₂ D}

theorem shift_ge (p y κ : ℝ) (hp : 2 ≤ p) (hκ : 0 ≤ κ) (hy0 : 0 ≤ y)
    (w : ℕ → ℝ) (hw : ∀ e, 0 ≤ w e) (Q : ℕ → Prop) [DecidablePred Q] :
    ∑' e : ℕ, (if Q e then max 0 (y / p ^ e - (w e + κ)) else 0) ≤
      ∑' e : ℕ, (if Q e then max 0 (y / p ^ e - w e) else 0) := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hr0 : (0 : ℝ) ≤ 1 / p := by positivity
  have hr1 : 1 / p < 1 := by rw [div_lt_one hp0]; linarith
  have hg : Summable (fun e : ℕ => y * (1 / p) ^ e) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left y
  have hs : ∀ c : ℕ → ℝ, (∀ e, 0 ≤ c e) →
      Summable (fun e => if Q e then max 0 (y / p ^ e - c e) else 0) := by
    intro c hc
    refine Summable.of_nonneg_of_le (fun e => ?_) (fun e => ?_) hg
    · split_ifs
      · exact le_max_left _ _
      · exact le_rfl
    · have hpe : y / p ^ e = y * (1 / p) ^ e := by rw [one_div_pow, div_eq_mul_one_div]
      split_ifs
      · exact max_le (mul_nonneg hy0 (by positivity)) (by rw [← hpe]; linarith [hc e])
      · exact mul_nonneg hy0 (by positivity)
  refine Summable.tsum_le_tsum (fun e => ?_) (hs _ fun e => by linarith [hw e]) (hs _ hw)
  split_ifs
  · exact max_le_max le_rfl (by linarith)
  · exact le_rfl

theorem shift_le (p y κ A : ℝ) (hp : 2 ≤ p) (hκ : 0 ≤ κ) (hy0 : 0 ≤ y) (hyA : y ≤ A) (hA : 1 ≤ A)
    (w : ℕ → ℝ) (hw : ∀ e, 1 ≤ w e) (Q : ℕ → Prop) [DecidablePred Q] (hQ : ∀ e, Q e → Odd e) :
    ∑' e : ℕ, (if Q e then max 0 (y / p ^ e - w e) else 0) ≤
      ∑' e : ℕ, (if Q e then max 0 (y / p ^ e - (w e + κ)) else 0) + κ * Real.logb p A := by
  have hp1 : (1 : ℝ) < p := by linarith
  have hp0 : (0 : ℝ) < p := by linarith
  have hr0 : (0 : ℝ) ≤ 1 / p := by positivity
  have hr1 : 1 / p < 1 := by rw [div_lt_one hp0]; linarith
  have hg : Summable (fun e : ℕ => y * (1 / p) ^ e) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left y
  have hs : ∀ c : ℕ → ℝ, (∀ e, 0 ≤ c e) →
      Summable (fun e => if Q e then max 0 (y / p ^ e - c e) else 0) := by
    intro c hc
    refine Summable.of_nonneg_of_le (fun e => ?_) (fun e => ?_) hg
    · split_ifs
      · exact le_max_left _ _
      · exact le_rfl
    · have hpe : y / p ^ e = y * (1 / p) ^ e := by rw [one_div_pow, div_eq_mul_one_div]
      split_ifs
      · exact max_le (mul_nonneg hy0 (by positivity)) (by rw [← hpe]; linarith [hc e])
      · exact mul_nonneg hy0 (by positivity)
  have hL0 : 0 ≤ Real.logb p A := Real.logb_nonneg hp1 hA
  set n := ⌊Real.logb p A⌋₊ with hn
  set ind : ℕ → ℝ := fun e => if Q e ∧ (p : ℝ) ^ e < A then 1 else 0 with hind
  have hlog : ∀ e : ℕ, (p : ℝ) ^ e < A → e ≤ n := by
    intro e he
    apply Nat.le_floor
    have h1 : Real.logb p ((p : ℝ) ^ e) = e := by
      rw [Real.logb_pow, Real.logb_self_eq_one hp1, mul_one]
    rw [← h1]
    exact (Real.logb_lt_logb hp1 (by positivity) he).le
  have hsupp : ∀ e ∉ Finset.range (n + 1), ind e = 0 := by
    intro e he
    simp only [hind]
    rw [ite_eq_right]
    rintro ⟨_, h⟩
    exact he (Finset.mem_range.2 (Nat.lt_succ_of_le (hlog e h)))
  have hind_sum : Summable ind := summable_of_ne_finset_zero hsupp
  have hcount : ∑' e, ind e ≤ Real.logb p A := by
    rw [tsum_eq_sum hsupp]
    have hsub : ∑ e ∈ Finset.range (n + 1), ind e ≤
        (((Finset.range (n + 1)).filter Odd).card : ℝ) := by
      rw [Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_le_sum fun e _ => ?_
      simp only [hind]
      split_ifs with h1 h2 <;> first | exact absurd (hQ e h1.1) h2 | norm_num
    have hodd : ((Finset.range (n + 1)).filter Odd).card ≤ n := by
      have h := Finset.card_le_card_of_injOn (fun e => e / 2) (s := (Finset.range (n + 1)).filter Odd) (t := Finset.range ((n + 1) / 2))
        (by
          intro e he
          have he' : e ≤ n ∧ Odd e := by simpa using he
          obtain ⟨h1, k, rfl⟩ := he'
          simp only [Finset.coe_range, Set.mem_Iio, Finset.mem_coe, Finset.mem_range]
          omega)
        (by
          intro e1 he1 e2 he2 heq
          have he1' : e1 ≤ n ∧ Odd e1 := by simpa using he1
          have he2' : e2 ≤ n ∧ Odd e2 := by simpa using he2
          obtain ⟨_, k1, rfl⟩ := he1'
          obtain ⟨_, k2, rfl⟩ := he2'
          simp only at heq
          omega)
      rw [Finset.card_range] at h
      omega
    calc ∑ e ∈ Finset.range (n + 1), ind e ≤ (((Finset.range (n + 1)).filter Odd).card : ℝ) := hsub
      _ ≤ (n : ℝ) := by exact_mod_cast hodd
      _ ≤ Real.logb p A := Nat.floor_le hL0
  have hterm : ∀ e, (if Q e then max 0 (y / p ^ e - w e) else 0) ≤
      (if Q e then max 0 (y / p ^ e - (w e + κ)) else 0) + κ * ind e := by
    intro e
    simp only [hind]
    by_cases hq : Q e
    · by_cases hu : 0 < y / p ^ e - w e
      · have hpA : (p : ℝ) ^ e < A := by
          have h1 : 1 < y / p ^ e := lt_of_le_of_lt (hw e) (by linarith)
          rw [lt_div_iff₀ (by positivity)] at h1
          linarith
        rw [ite_eq_left hq, ite_eq_left hq, ite_eq_left ⟨hq, hpA⟩, max_eq_right hu.le]
        have := le_max_right 0 (y / p ^ e - (w e + κ))
        linarith
      · rw [ite_eq_left hq, ite_eq_left hq, max_eq_left (not_lt.1 hu)]
        have h1 := le_max_left 0 (y / p ^ e - (w e + κ))
        have h2 : 0 ≤ κ * (if Q e ∧ (p : ℝ) ^ e < A then (1 : ℝ) else 0) :=
          mul_nonneg hκ (by split_ifs <;> norm_num)
        linarith
    · rw [ite_eq_right hq, ite_eq_right hq, ite_eq_right (fun h => hq h.1)]
      simp
  have hsκ := hs (fun e => w e + κ) (fun e => by linarith [hw e])
  calc ∑' e, (if Q e then max 0 (y / p ^ e - w e) else 0)
      ≤ ∑' e, ((if Q e then max 0 (y / p ^ e - (w e + κ)) else 0) + κ * ind e) :=
        Summable.tsum_le_tsum hterm (hs _ fun e => by linarith [hw e]) (hsκ.add (hind_sum.mul_left κ))
    _ = ∑' e, (if Q e then max 0 (y / p ^ e - (w e + κ)) else 0) + κ * ∑' e, ind e := by
        rw [Summable.tsum_add hsκ (hind_sum.mul_left κ), tsum_mul_left]
    _ ≤ ∑' e, (if Q e then max 0 (y / p ^ e - (w e + κ)) else 0) + κ * Real.logb p A :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hcount hκ)

theorem n_pos (D : D7) : 1 ≤ D.R.n := by
  have h1 := D.R.two_le_m
  have h2 := D.R.m_le_f
  unfold Formalism.BasicNotions.Ranks.n
  omega

theorem fill_ge (X : Inst D L) (b : HH D → ℤ) (hb : ∀ t ∈ D.host.TT, (0 : ℝ) ≤ (b t : ℝ)) (j : ℕ)
    (z : Bool × HH D) : L.sc.w'' D.R.n ≤ fill X b j z := by
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hL0 : 0 ≤ L.sc.L := by
    show 0 ≤ L.sc.x ^ L.sc.eps
    exact Real.rpow_nonneg (by linarith) _
  have hb1 : 1 ≤ L.sc.b := by
    show 1 ≤ Real.exp L.sc.L
    exact Real.one_le_exp hL0
  have ha1 : 1 ≤ L.sc.a := by
    show 1 ≤ L.sc.x * L.sc.b
    nlinarith
  have hX1 : 1 ≤ L.sc.X' := by
    show 1 ≤ Real.exp (L.sc.x ^ (L.sc.eps / 3))
    exact Real.one_le_exp (Real.rpow_nonneg (by linarith) _)
  have hb'0 : 0 ≤ L.sc.b' := by
    show 0 ≤ L.sc.a / L.sc.X'
    exact div_nonneg (by linarith) (by linarith)
  have hn : (1 : ℝ) ≤ D.R.n := by exact_mod_cast n_pos D
  have hw1 : L.sc.w'' D.R.n ≤ L.sc.b' / L.sc.x := by
    show L.sc.b' / (L.sc.x * D.R.n) ≤ L.sc.b' / L.sc.x
    exact div_le_div_of_nonneg_left hb'0 (by linarith) (by nlinarith)
  have hw2 : L.sc.w'' D.R.n ≤ L.sc.b := by
    calc L.sc.w'' D.R.n ≤ L.sc.b' / L.sc.x := hw1
      _ = L.sc.b / L.sc.X' := by
        show L.sc.x * L.sc.b / L.sc.X' / L.sc.x = L.sc.b / L.sc.X'
        field_simp
      _ ≤ L.sc.b := div_le_self (by linarith) hX1
  unfold fill
  by_cases htop : IsTopPl D z
  · rw [ite_eq_left (show z.1 = false ∧ z.2 ∈ D.host.TT from htop)]
    linarith [hb z.2 htop.2, (X.off_top j z htop).1]
  · rw [ite_eq_right (show ¬(z.1 = false ∧ z.2 ∈ D.host.TT) from htop), zero_add]
    by_cases hthick : IsThickPl D z
    · linarith [(X.off_thick j z hthick).1]
    · exact (X.off_thin j z ⟨htop, hthick⟩).1

theorem kaJ_bounds (D : D7) (j : ℕ) (hj : j ∈ SizeData₂.lifts D) : 0 ≤ kaJ D j ∧ kaJ D j ≤ Nm D := by
  simp only [Formalism.BasicNotions.SizeData₂.lifts, Finset.mem_Icc] at hj
  obtain ⟨h1, h2⟩ := hj
  have h1' : (1 : ℝ) ≤ j := by exact_mod_cast h1
  have h2' : (j : ℝ) ≤ D.R.m := by exact_mod_cast h2
  have ht : (0 : ℝ) ≤ D.R.t + 1 := by positivity
  unfold kaJ Nm Formalism.BasicNotions.Ranks.N
  push_cast
  constructor
  · apply div_nonneg _ (by norm_num)
    nlinarith
  · rw [div_le_iff₀ (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_right (show 2 * (j : ℝ) - 1 ≤ 2 * D.R.m by linarith) ht]

theorem asksAll_of (X : Inst D L) (hSz : Nm D + 1 ≤ L.sc.w'' D.R.n) : RequiresAll X := by
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hL0 : 0 ≤ L.sc.L := by
    show 0 ≤ L.sc.x ^ L.sc.eps
    exact Real.rpow_nonneg (by linarith) _
  have hb1 : 1 ≤ L.sc.b := by
    show 1 ≤ Real.exp L.sc.L
    exact Real.one_le_exp hL0
  have ha1 : 1 ≤ L.sc.a := by
    show 1 ≤ L.sc.x * L.sc.b
    nlinarith
  intro a b ha hb p hp j hj s hs
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  obtain ⟨hk0, hkN⟩ := kaJ_bounds D j hj
  have hNm0 : (0 : ℝ) ≤ Nm D := by unfold Nm; positivity
  have hwG : ∀ e, 1 ≤ fillG X b j (partner D p s e) := by
    intro e
    have := fill_ge X b hb j (partner D p s e)
    unfold fillG
    linarith
  have hw0 : ∀ e, 0 ≤ fillG X b j (partner D p s e) := fun e => by linarith [hwG e]
  have hwF : ∀ e, 0 ≤ fill X b j (partner D p s e) := fun e => by
    have := fill_ge X b hb j (partner D p s e)
    linarith
  have hA : 1 ≤ 2 * L.sc.a := by linarith
  have hlog : 0 ≤ Real.logb p (2 * L.sc.a) := Real.logb_nonneg (by linarith) hA
  by_cases hy : 0 ≤ (a s : ℝ)
  · have h1 := shift_ge (p : ℝ) (a s) (kaJ D j) hp2 hk0 hy
      (fun e => fillG X b j (partner D p s e)) hw0 Odd
    have h2 := shift_le (p : ℝ) (a s) (kaJ D j) (2 * L.sc.a) hp2 hk0 hy (ha s hs) hA
      (fun e => fillG X b j (partner D p s e)) hwG Odd (fun e h => h)
    simp only [fillG, sub_add_cancel] at h1 h2
    unfold askP askG fillG
    refine ⟨h1, ?_⟩
    nlinarith [mul_le_mul_of_nonneg_right hkN hlog]
  · have hz : ∀ c : ℕ → ℝ, (∀ e, 0 ≤ c e) →
        ∑' e : ℕ, (if Odd e then max 0 ((a s : ℝ) / (p : ℝ) ^ e - c e) else 0) = 0 := by
      intro c hc
      refine (tsum_congr fun e => ?_).trans tsum_zero
      split_ifs
      · apply max_eq_left
        have : (a s : ℝ) / (p : ℝ) ^ e ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
        linarith [hc e]
      · rfl
    have e1 := hz (fun e => fill X b j (partner D p s e)) hwF
    have e2 := hz (fun e => fillG X b j (partner D p s e)) hw0
    beta_reduce at e1 e2
    unfold askP askG
    rw [e1, e2]
    exact ⟨le_rfl, by rw [zero_add]; exact mul_nonneg hNm0 hlog⟩

theorem lo_succ (K : Consts) (hLa : 0 ≤ K.La) (L : SizeData₂ D) (C bo : ℝ) (p : ℕ) (hp : p.Prime) :
    lo K L C bo p + (cG L + L.etaSz) * Real.logb p (2 * L.sc.a) ≤ lo K L (C + 1) bo p := by
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hL0 : 0 ≤ L.sc.L := by
    show 0 ≤ L.sc.x ^ L.sc.eps
    exact Real.rpow_nonneg (by linarith) _
  have hb1 : 1 ≤ L.sc.b := by
    show 1 ≤ Real.exp L.sc.L
    exact Real.one_le_exp hL0
  have ha1 : 1 ≤ L.sc.a := by
    show 1 ≤ L.sc.x * L.sc.b
    nlinarith
  have hX1 : 1 ≤ L.sc.X' := by
    show 1 ≤ Real.exp (L.sc.x ^ (L.sc.eps / 3))
    exact Real.one_le_exp (Real.rpow_nonneg (by linarith) _)
  have hb'0 : 0 ≤ L.sc.b' := by
    show 0 ≤ L.sc.a / L.sc.X'
    exact div_nonneg (by linarith) (by linarith)
  have hlogx : 0 ≤ Real.log L.sc.x := Real.log_nonneg hx1.le
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  have hw : 0 ≤ L.sc.w'' D.R.n := by
    show 0 ≤ L.sc.b' / (L.sc.x * D.R.n)
    exact div_nonneg hb'0 (mul_nonneg (by linarith) (Nat.cast_nonneg _))
  have hd1 : 0 < L.sc.delta1 := by
    show 0 < L.sc.x ^ (-(L.sc.eps / 8))
    exact Real.rpow_pos_of_pos (by linarith) _
  have hLaS : 0 ≤ La K L.sc := by
    unfold La
    exact mul_nonneg (mul_nonneg hLa (by positivity)) (Real.log_nonneg ha1)
  have g1 : 0 ≤ (rG L.sc : ℝ) * L.sc.b' * Real.log L.sc.x :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hb'0) hlogx
  have g2 : 0 ≤ L.sc.w'' D.R.n * Real.log L.sc.x / L.sc.delta1 :=
    div_nonneg (mul_nonneg hw hlogx) hd1.le
  have g3 : 0 ≤ La K L.sc * L.sc.a / ((p : ℝ) * D.R.k) :=
    div_nonneg (mul_nonneg hLaS (by linarith)) (mul_nonneg hp0 (Nat.cast_nonneg _))
  have g4 : 0 ≤ L.sc.a * (p : ℝ) ^ (-(L1 D L.sc p : ℝ)) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg hp0 _)
  have g5 : 0 ≤ L.sc.a / (p : ℝ) ^ 2 := div_nonneg (by linarith) (by positivity)
  have g6 := mul_nonneg hlogx (add_nonneg g3 g4)
  have g7 := mul_nonneg hlogx (add_nonneg g3 g5)
  obtain ⟨α, β, hform, hα⟩ : ∃ α β : ℝ, (∀ C' : ℝ, lo K L C' bo p = C' * α + β) ∧
      (cG L + L.etaSz) * Real.logb p (2 * L.sc.a) ≤ α :=
    ⟨(cG L + L.etaSz) * Real.logb p (2 * L.sc.a) +
        (if IsResidueClassZero D p then (if (p : ℝ) < L.sc.p0 D.R.k then (rG L.sc : ℝ) * L.sc.b' * Real.log L.sc.x
          else if (p : ℝ) < L.sc.X' then L.sc.w'' D.R.n * Real.log L.sc.x / L.sc.delta1 else 0)
          else 0) +
        (if IsResidueClassZero D p ∧ (p : ℝ) < L.sc.X' then Real.log L.sc.x * (La K L.sc * L.sc.a / ((p : ℝ) * D.R.k) +
          (if (p : ℝ) < L.sc.p0 D.R.k then L.sc.a * (p : ℝ) ^ (-(L1 D L.sc p : ℝ))
            else L.sc.a / (p : ℝ) ^ 2)) else 0),
      (if IsResidueClassZero D p then (if (p : ℝ) < L.sc.p0 D.R.k then 0
        else if (p : ℝ) < L.sc.X' then L.sc.b' / L.sc.x + L.etaSz + bo else 0) else 0),
      fun C' => by
        simp only [lo]
        split_ifs <;> ring,
      by split_ifs <;> linarith [g1, g2, g6, g7]⟩
  rw [hform, hform]
  have e : (C + 1) * α + β = C * α + β + α := by ring
  rw [e]
  linarith

theorem fl_succ (D : D7) (s : Scale) (C : ℝ) (p : ℕ) (hp : p.Prime) : fl D s C p ≤ fl D s (C + 1) p := by
  have hx1 : 1 < s.x := s.one_lt_alt
  have hL0 : 0 ≤ s.L := by
    show 0 ≤ s.x ^ s.eps
    exact Real.rpow_nonneg (by linarith) _
  have hb1 : 1 ≤ s.b := by
    show 1 ≤ Real.exp s.L
    exact Real.one_le_exp hL0
  have ha1 : 1 ≤ s.a := by
    show 1 ≤ s.x * s.b
    nlinarith
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hl : 0 ≤ Real.logb p s.a := Real.logb_nonneg hp1 ha1
  have h1 : 0 ≤ (D.R.f : ℝ) * Nm D ^ 2 * Real.logb p s.a := mul_nonneg (by positivity) hl
  have h2 : 0 ≤ (D.R.f : ℝ) * Real.logb p s.a ^ 2 := by positivity
  unfold fl
  nlinarith [h1, h2]

theorem TTP_subset₂ (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) : TTP X K a b p ⊆ D.host.TT := by
  unfold TTP
  split_ifs
  · exact Finset.Subset.refl _
  · exact Finset.filter_subset _ _

theorem gainBoundAll_add_one_of_gainBoundAllRequired (X : Inst D L) (K : Consts) (hLa : 0 ≤ K.La) (C bo : ℝ) (hA : RequiresAll X) (hNc : Nm D ≤ cG L)
    (h : GainBoundAllUniform X K C bo) : GainBoundAll X K (C + 1) bo := by
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hL0 : 0 ≤ L.sc.L := by
    show 0 ≤ L.sc.x ^ L.sc.eps
    exact Real.rpow_nonneg (by linarith) _
  have hb1 : 1 ≤ L.sc.b := by
    show 1 ≤ Real.exp L.sc.L
    exact Real.one_le_exp hL0
  have ha1 : 1 ≤ L.sc.a := by
    show 1 ≤ L.sc.x * L.sc.b
    nlinarith
  have hX1 : 1 ≤ L.sc.X' := by
    show 1 ≤ Real.exp (L.sc.x ^ (L.sc.eps / 3))
    exact Real.one_le_exp (Real.rpow_nonneg (by linarith) _)
  have hb'0 : 0 ≤ L.sc.b' := by
    show 0 ≤ L.sc.a / L.sc.X'
    exact div_nonneg (by linarith) (by linarith)
  intro a b hwin p hp hcls hX
  obtain ⟨hgain, hsum⟩ := h a b hwin p hp hcls hX
  refine ⟨hgain, ?_⟩
  have hlo := lo_succ K hLa L C bo p hp
  have hfl := fl_succ D L.sc C p hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlog : 0 ≤ Real.logb p (2 * L.sc.a) := Real.logb_nonneg hp1 (by linarith)
  have heta := L.etaSz_pos
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hxA : 1 ≤ L.sc.x ^ (Scale.A / 2) :=
    Real.one_le_rpow hx1.le (by unfold Scale.A; norm_num)
  have ha2 : ∀ t ∈ D.host.TT, (a t : ℝ) ≤ 2 * L.sc.a := by
    intro t ht
    have h1 := (hwin t ht).2.1
    have h2 : L.sc.a / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)) ≤ L.sc.a :=
      div_le_self (by linarith) (one_le_mul_of_one_le_of_one_le hk1 hxA)
    linarith
  have hb0 : ∀ t ∈ D.host.TT, (0 : ℝ) ≤ (b t : ℝ) := fun t ht => by
    linarith [(hwin t ht).2.2]
  have hterm : ∀ j ∈ SizeData₂.lifts D, ∀ s ∈ TTP X K a b p,
      askG X a b p j s - lo K L (C + 1) bo p ≤ askP X a b p j s - lo K L C bo p := by
    intro j hj s hs
    have hA := (hA a b ha2 hb0 p hp j hj s (TTP_subset₂ X K a b p hs)).2
    have h3 : Nm D * Real.logb p (2 * L.sc.a) ≤ (cG L + L.etaSz) * Real.logb p (2 * L.sc.a) :=
      mul_le_mul_of_nonneg_right (by linarith) hlog
    linarith
  have hsum2 : (∑ j ∈ SizeData₂.lifts D, ∑ s ∈ TTP X K a b p, (askG X a b p j s - lo K L (C + 1) bo p)) ≤
      ∑ j ∈ SizeData₂.lifts D, ∑ s ∈ TTP X K a b p, (askP X a b p j s - lo K L C bo p) :=
    Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun s hs => hterm j hj s hs
  have hm : 0 ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hfl hm]

end Formalism.MainNotions.AuxBlock8.Pf.As

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.GainBoundAllAddOneOfGainBoundAllRequired =====

-- ===== clump member: Formalism.SharpRestriction.GrowthBounds.LogarithmicSums =====
-- clump-header: {"m": "Formalism.SharpRestriction.GrowthBounds.LogarithmicSums", "h": "module\n\npublic import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.RemainingCountingStatement\npublic import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.GainBoundAllAddOneOfGainBoundAllRequired\npublic import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.NotSingularOfCentral\npublic import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.PartnerCountOfCentral\npublic import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.MeanNum\npublic import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.StarFam\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G

namespace Formalism.MainNotions.AuxBlock8.Pf

def RestStar {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ K : Consts, K.Nonneg → ∀ C31 Ce Cm : ℝ, 0 < C31 → ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ C ≥ C0,
    ∀ (X : ∀ x (i : Fm.Ix x), Inst (Fm.D x i) (Fm.L x i)) (Y : ∀ x (i : Fm.Ix x), LatInst (Fm.D x i)),
      AdmFam Fm K X Y C31 Ce Cm → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
        StarAll (X x i) K C ((Fm.L x i).sc.b ^ (x ^ (-(eps / 2))))

theorem bo_nonneg (s : Scale) (y : ℝ) : 0 ≤ s.b ^ y := Real.rpow_nonneg (Real.exp_pos s.L).le y

private theorem eventually_adm_of_admFam {eps : ℝ} (Fm : FamP eps) {K : Consts}
    {X : ∀ x (i : Fm.Ix x), Inst (Fm.D x i) (Fm.L x i)} {Y : ∀ x (i : Fm.Ix x), LatInst (Fm.D x i)}
    {C31 Ce Cm : ℝ} (hA : AdmFam Fm K X Y C31 Ce Cm) :
    ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x ∧
      ∀ i : Fm.Ix x, admitted (Fm.D x i) (Fm.L x i) (X x i) (Y x i) K ⟨C31, Ce, Cm, 1⟩ := by
  obtain ⟨x0, -, h⟩ := hA 1 one_pos
  refine ⟨max x0 (Fm.x1 + 1), fun x hx => ⟨?_, h x (le_trans (le_max_left _ _) hx)⟩⟩
  linarith [le_trans (le_max_right _ _) hx]

theorem rest0 {eps : ℝ} (Fm : FamP eps) : FamilyAskBounds Fm := by
  intro K _ C31 Ce Cm _ _ _ X Y hA
  obtain ⟨x0, h⟩ := eventually_adm_of_admFam Fm hA
  refine ⟨x0, fun x hx i => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, hSz⟩ := (h x hx).2 i
  exact As.asksAll_of (X x i) hSz.2.2

theorem remainingCountingStatement_of_restStar {eps : ℝ} (Fm : FamP eps) (hS : RestStar Fm) : RemainingCountingStatement Fm := by
  intro K hK C31 Ce Cm hC31 hCe _
  obtain ⟨C0, hC0, hS'⟩ := hS K hK C31 Ce Cm hC31
  obtain ⟨C1, hC01, h3, hd1, hd2⟩ : ∃ C1 : ℝ, C0 ≤ C1 ∧ 3 ≤ C1 ∧ 2 * K.dl1 + (Ce + 1) ≤ C1 ∧
      4 * K.dl2 ≤ C1 :=
    ⟨max C0 (max 3 (max (2 * K.dl1 + (Ce + 1)) (4 * K.dl2))), le_max_left _ _,
      le_trans (le_max_left _ _) (le_max_right _ _),
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _),
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)⟩
  refine ⟨C1 + 1, by linarith, fun X Y hA => ?_⟩
  obtain ⟨x1, h1⟩ := hS' C1 hC01 X Y hA
  obtain ⟨x2, h2⟩ := eventually_adm_of_admFam Fm hA
  refine ⟨max x1 x2, fun x hx i => ?_⟩
  obtain ⟨hxp, hadm⟩ := h2 x (le_trans (le_max_right _ _) hx)
  obtain ⟨-, -, -, -, -, -, a9, -, -, aSz⟩ := hadm i
  have hN : GainBoundConstants K (Ce + 1) C1 ((Fm.L x i).sc.b ^ (x ^ (-(eps / 2)))) :=
    ⟨h3, hd1, hd2, bo_nonneg _ _⟩
  have hP := gain_bound_all_of_star (Fm.params x hxp i) (X x i) K hK Ce C1 _ hCe hN a9
    (h1 x (le_trans (le_max_left _ _) hx) i)
  have hNc : Nm (Fm.D x i) ≤ cG (Fm.L x i) :=
    (basics (Fm.params x hxp i)).2.1.trans (St.base (Fm.params x hxp i)).2.2.2.2
  exact As.gainBoundAll_add_one_of_gainBoundAllRequired (X x i) K hK.1 C1 _ (As.asksAll_of (X x i) aSz.2.2) hNc hP

theorem rest2 {eps : ℝ} (Fm : FamP eps) : FamilyFourthBound Fm := by
  intro K hK C31 Ce Cm _ _ hCm X Y hA
  obtain ⟨x0, h⟩ := second_estimate_and_mean_along_family Fm K hK C31 Ce Cm hCm X Y hA
  exact ⟨x0, fun x hx i => (h x hx i).1⟩

theorem restStar {eps : ℝ} (Fm : FamP eps) : RestStar Fm := by
  exact St.star_fam Fm

theorem stmtEF {eps : ℝ} (Fm : FamP eps) : FamilyClosedForm Fm :=
  stmtEF_of Fm (rest0 Fm) (remainingCountingStatement_of_restStar Fm (restStar Fm)) (rest2 Fm)

theorem stmtF {eps : ℝ} (Fm : FamP eps) : KudlaFamilyStatement Fm :=
  stmtF_of_stmtEF Fm (stmtEF Fm)

end Formalism.MainNotions.AuxBlock8.Pf

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.SharpRestriction.GrowthBounds.LogarithmicSums =====
