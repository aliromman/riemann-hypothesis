module

public import GroundTheory.PAdicHodge.NormalizedTraceTower
public import GroundTheory.PAdicHodge.NormalizedTraceClosure
public import GroundTheory.PAdicHodge.NormalizedTrace
public import GroundTheory.PAdicHodge.CyclotomicField
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormNatCastPrime
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
public import GroundTheory.PAdicHodge.TateCpTwist
public import GroundTheory.PAdicHodge.AxLemma
import GroundTheory.PAdicHodge.GaloisOnCp
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Algebra.Order.Star.Int
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: GroundTheory.PAdicHodge.CyclotomicTower, GroundTheory.PAdicHodge.TateNormalizedTrace, GroundTheory.PAdicHodge.ExistsGalFixCyclotomicLayerCycloCharNeOne

-- ===== clump member: GroundTheory.PAdicHodge.CyclotomicTower =====
-- clump-header: {"m": "GroundTheory.PAdicHodge.CyclotomicTower", "h": "module\n\npublic import GroundTheory.PAdicHodge.NormalizedTrace\npublic import GroundTheory.PAdicHodge.CyclotomicField\npublic import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic\npublic import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormNatCastPrime\nimport GroundTheory.PAdicHodge.GaloisOnCp\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.RingTheory.SimpleRing.Principal\npublic import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval\n\n"}
section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

open IntermediateField Polynomial Module

noncomputable section

variable {p : ℕ} [Fact p.Prime]

theorem norm_eq_one_of_pow_eq_one {x : PadicAlgCl p} {N : ℕ} (hN : N ≠ 0) (hx : x ^ N = 1) :
    ‖x‖ = 1 := by
  have h : ‖x‖ ^ N = 1 := by rw [← norm_pow, hx, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg x) hN).1 h

theorem norm_pow_sub_one_le {ζ : PadicAlgCl p} {N : ℕ} (hN : N ≠ 0) (hζ : ζ ^ N = 1) (j : ℕ) :
    ‖ζ ^ j - 1‖ ≤ ‖ζ - 1‖ := by
  have h1 : ‖ζ‖ = 1 := norm_eq_one_of_pow_eq_one hN hζ
  rw [← geom_sum_mul, norm_mul]
  have : ‖∑ i ∈ Finset.range j, ζ ^ i‖ ≤ 1 :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => by
      rw [norm_pow, h1, one_pow]
  calc _ ≤ 1 * ‖ζ - 1‖ := mul_le_mul_of_nonneg_right this (norm_nonneg _)
    _ = _ := one_mul _

theorem norm_sub_one_eq_of_isPrimitiveRoot {ζ η : PadicAlgCl p} {N : ℕ} (hN : N ≠ 0)
    (hζ : IsPrimitiveRoot ζ N) (hη : IsPrimitiveRoot η N) : ‖η - 1‖ = ‖ζ - 1‖ := by
  have : NeZero N := ⟨hN⟩
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hη.pow_eq_one
  obtain ⟨j, -, hj⟩ := hη.eq_pow_of_pow_eq_one hζ.pow_eq_one
  refine le_antisymm (norm_pow_sub_one_le hN hζ.pow_eq_one i) ?_
  conv_lhs => rw [← hj]
  exact norm_pow_sub_one_le hN hη.pow_eq_one j

theorem norm_sub_one_pow_totient {ζ : PadicAlgCl p} {k : ℕ}
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) :
    ‖ζ - 1‖ ^ Nat.totient (p ^ (k + 1)) = (p : ℝ)⁻¹ := by
  have hpos : 0 < p ^ (k + 1) := pow_pos (Fact.out : p.Prime).pos _
  have h1 := congrArg (eval 1) (cyclotomic_eq_prod_X_sub_primitiveRoots hζ)
  rw [eval_one_cyclotomic_prime_pow, eval_prod] at h1
  simp only [eval_sub, eval_X, eval_C] at h1
  rw [← _root_.UpperTheory.Reformulated.B.CapelliMiscellany.norm_natCast_prime]
  calc ‖ζ - 1‖ ^ Nat.totient (p ^ (k + 1))
      = ∏ _μ ∈ primitiveRoots (p ^ (k + 1)) (PadicAlgCl p), ‖ζ - 1‖ := by
        rw [Finset.prod_const, hζ.card_primitiveRoots]
    _ = ∏ μ ∈ primitiveRoots (p ^ (k + 1)) (PadicAlgCl p), ‖1 - μ‖ :=
        Finset.prod_congr rfl fun μ hμ => by
          rw [norm_sub_rev 1 μ]
          exact (norm_sub_one_eq_of_isPrimitiveRoot hpos.ne' hζ
            ((mem_primitiveRoots hpos).1 hμ)).symm
    _ = _ := by rw [h1, norm_prod]

theorem norm_sub_one_le_one {ζ : PadicAlgCl p} {N : ℕ} (hN : N ≠ 0) (hζ : ζ ^ N = 1) :
    ‖ζ - 1‖ ≤ 1 := by
  have := IsUltrametricDist.norm_add_le_max ζ (-1)
  rw [← sub_eq_add_neg, norm_neg, norm_one, norm_eq_one_of_pow_eq_one hN hζ, max_self] at this
  exact this

theorem norm_pow_natDegree_minpoly (y : PadicAlgCl p) :
    ‖y‖ ^ (minpoly ℚ_[p] y).natDegree = ‖(minpoly ℚ_[p] y).coeff 0‖ := by
  have hd : (minpoly ℚ_[p] y).natDegree ≠ 0 :=
    (minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral y)).ne'
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow, one_div,
    Real.rpow_inv_natCast_pow (norm_nonneg _) hd]

theorem exists_norm_eq_zpow_of_ne_zero {c : ℚ_[p]} (hc : c ≠ 0) : ∃ z : ℤ, ‖c‖ = (p : ℝ) ^ z :=
  ⟨-c.valuation, Padic.norm_eq_zpow_neg_valuation hc⟩

theorem one_lt_p_real : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt

theorem zpow_p_injective : Function.Injective fun z : ℤ => (p : ℝ) ^ z :=
  zpow_right_injective₀ (by linarith [one_lt_p_real (p := p)]) (one_lt_p_real (p := p)).ne'

theorem minpoly_eq_cyclotomic_of_isPrimitiveRoot {ζ : PadicAlgCl p} {k : ℕ}
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) :
    minpoly ℚ_[p] ζ = cyclotomic (p ^ (k + 1)) ℚ_[p] := by
  have hpos : 0 < p ^ (k + 1) := pow_pos (Fact.out : p.Prime).pos _
  have hint : IsIntegral ℚ_[p] ζ := Algebra.IsIntegral.isIntegral ζ
  have hdvd : minpoly ℚ_[p] ζ ∣ cyclotomic (p ^ (k + 1)) ℚ_[p] := by
    apply minpoly.dvd
    rw [aeval_def, ← eval_map, map_cyclotomic]
    exact hζ.isRoot_cyclotomic hpos
  set d := (minpoly ℚ_[p] ζ).natDegree with hd
  have hφ : 0 < Nat.totient (p ^ (k + 1)) := Nat.totient_pos.2 hpos
  have hd0 : 0 < d := minpoly.natDegree_pos hint

  have hπdeg : (minpoly ℚ_[p] (ζ - 1)).natDegree = d := by
    have : ζ - 1 = ζ - algebraMap ℚ_[p] (PadicAlgCl p) 1 := by rw [map_one]
    rw [this, minpoly.sub_algebraMap, natDegree_comp, natDegree_X_add_C, mul_one]
  have hπ0 : ζ - 1 ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    have := hζ.pow_ne_one_of_pos_of_lt one_ne_zero (Nat.one_lt_pow (Nat.succ_ne_zero k)
      (Fact.out : p.Prime).one_lt)
    exact this (by rw [pow_one, h])
  have hc0 : (minpoly ℚ_[p] (ζ - 1)).coeff 0 ≠ 0 :=
    minpoly.coeff_zero_ne_zero (Algebra.IsIntegral.isIntegral _) hπ0
  obtain ⟨z, hz⟩ := exists_norm_eq_zpow_of_ne_zero hc0
  have e1 := norm_pow_natDegree_minpoly (ζ - 1)
  rw [hπdeg, hz] at e1
  have e2 := norm_sub_one_pow_totient hζ

  have key : (p : ℝ) ^ (z * Nat.totient (p ^ (k + 1))) = (p : ℝ) ^ (-(d : ℤ)) := by
    calc (p : ℝ) ^ (z * Nat.totient (p ^ (k + 1)))
        = ((p : ℝ) ^ z) ^ Nat.totient (p ^ (k + 1)) := by rw [zpow_mul, zpow_natCast]
      _ = (‖ζ - 1‖ ^ d) ^ Nat.totient (p ^ (k + 1)) := by rw [e1]
      _ = (‖ζ - 1‖ ^ Nat.totient (p ^ (k + 1))) ^ d := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ = ((p : ℝ)⁻¹) ^ d := by rw [e2]
      _ = (p : ℝ) ^ (-(d : ℤ)) := by rw [zpow_neg, zpow_natCast, inv_pow]
  have key' := zpow_p_injective (p := p) key
  have hdvdφ : Nat.totient (p ^ (k + 1)) ∣ d := by
    have : ((Nat.totient (p ^ (k + 1)) : ℕ) : ℤ) ∣ (d : ℤ) :=
      ⟨-z, by linear_combination key'⟩
    exact Int.natCast_dvd_natCast.1 this
  have hle1 : Nat.totient (p ^ (k + 1)) ≤ d := Nat.le_of_dvd hd0 hdvdφ
  have hle2 : d ≤ Nat.totient (p ^ (k + 1)) := by
    rw [← natDegree_cyclotomic (p ^ (k + 1)) ℚ_[p]]
    exact natDegree_le_of_dvd hdvd (cyclotomic_ne_zero _ _)
  exact (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (cyclotomic.monic _ _) hdvd
    (by rw [natDegree_cyclotomic]; omega)).symm

theorem finrank_cycl (n : ℕ) : finrank ℚ_[p] (cycl p n) = Nat.totient (p ^ n) := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot (p := p) n
  rw [cycl_eq_adjoin hζ, IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral ζ)]
  cases n with
  | zero =>
    rw [pow_zero, IsPrimitiveRoot.one_right_iff] at hζ
    subst hζ
    rw [minpoly.one]
    simpa using natDegree_X_sub_C (1 : ℚ_[p])
  | succ k => rw [minpoly_eq_cyclotomic_of_isPrimitiveRoot hζ, natDegree_cyclotomic]

theorem totient_prime_pow_succ {k : ℕ} (hk : 1 ≤ k) :
    Nat.totient (p ^ (k + 1)) = p * Nat.totient (p ^ k) := by
  rw [pow_succ', Nat.totient_mul_of_dvd (dvd_pow_self p (by omega))]

theorem natDegree_minpoly_cycl_of_adjoin_eq {k : ℕ} (hk : 1 ≤ k) {y : PadicAlgCl p}
    (hy : ℚ_[p]⟮y⟯ = cycl p (k + 1)) : (minpoly (cycl p k) y).natDegree = p := by
  have hint : IsIntegral (cycl p k) y :=
    (Algebra.IsIntegral.isIntegral (R := ℚ_[p]) y).tower_top
  have e := finrank_sup_adjoin_simple (cycl p k) hint
  rw [hy, sup_eq_right.2 (cycl_mono (Nat.le_succ k)), finrank_cycl, finrank_cycl,
    totient_prime_pow_succ hk] at e
  have hφ : 0 < Nat.totient (p ^ k) := Nat.totient_pos.2 (pow_pos (Fact.out : p.Prime).pos _)
  rw [mul_comm p] at e
  exact (Nat.eq_of_mul_eq_mul_left hφ e).symm

theorem normTrace_cycl_isPrimitiveRoot {k : ℕ} (hk : 1 ≤ k) {η : PadicAlgCl p}
    (hη : IsPrimitiveRoot η (p ^ (k + 1))) : normTrace (cycl p k) η = 0 := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hint : IsIntegral (cycl p k) η :=
    (Algebra.IsIntegral.isIntegral (R := ℚ_[p]) η).tower_top
  have hdeg := natDegree_minpoly_cycl_of_adjoin_eq hk (cycl_eq_adjoin hη).symm
  have hc : η ^ p ∈ cycl p k := pow_eq_one_mem_cycl (by rw [← pow_mul, ← pow_succ']; exact hη.pow_eq_one)
  set f : (cycl p k)[X] := X ^ p - C ⟨η ^ p, hc⟩ with hf
  have hfm : f.Monic := monic_X_pow_sub_C _ (by omega)
  have hfdeg : f.natDegree = p := natDegree_X_pow_sub_C _
  have hroot : aeval η f = 0 := by simp [hf]
  have hdvd : minpoly (cycl p k) η ∣ f := minpoly.dvd _ _ hroot
  have heq : f = minpoly (cycl p k) η :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hfm hdvd (by rw [hfdeg, hdeg])
  have hnext : f.nextCoeff = 0 := by
    rw [nextCoeff_of_natDegree_pos (by omega), hfdeg, hf, coeff_sub, coeff_X_pow, coeff_C]
    simp only [ite_eq_right (show p - 1 ≠ p by omega), ite_eq_right (show p - 1 ≠ 0 by omega), sub_zero]
  rw [normTrace, normTraceF, ← heq, hnext]
  simp

theorem exists_norm_pow_totient_eq_zpow {n : ℕ} {y : PadicAlgCl p} (hy : y ∈ cycl p n)
    (hy0 : y ≠ 0) : ∃ z : ℤ, ‖y‖ ^ Nat.totient (p ^ n) = (p : ℝ) ^ z := by
  have hint : IsIntegral ℚ_[p] y := Algebra.IsIntegral.isIntegral y
  have hle : ℚ_[p]⟮y⟯ ≤ cycl p n := by rw [adjoin_simple_le_iff]; exact hy
  have hdvd : (minpoly ℚ_[p] y).natDegree ∣ Nat.totient (p ^ n) := by
    rw [← finrank_cycl, finrank_eq_mul_finrank_extendScalars hle,
      IntermediateField.adjoin.finrank hint]
    exact Dvd.intro _ rfl
  obtain ⟨m, hm⟩ := hdvd
  have hc0 : (minpoly ℚ_[p] y).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hy0
  obtain ⟨z, hz⟩ := exists_norm_eq_zpow_of_ne_zero hc0
  refine ⟨z * m, ?_⟩
  rw [hm, pow_mul, norm_pow_natDegree_minpoly, hz, zpow_mul, zpow_natCast]


variable (p) in
def cyclRadius (p : ℕ) [Fact p.Prime] (j : ℕ) : ℝ :=
  ‖(exists_isPrimitiveRoot (p := p) j).choose - 1‖

theorem norm_sub_one_eq_cyclRadius {η : PadicAlgCl p} {j : ℕ} (hη : IsPrimitiveRoot η (p ^ j)) :
    ‖η - 1‖ = cyclRadius p j :=
  norm_sub_one_eq_of_isPrimitiveRoot (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
    (exists_isPrimitiveRoot (p := p) j).choose_spec hη

theorem cyclRadius_nonneg (j : ℕ) : 0 ≤ cyclRadius p j := norm_nonneg _

theorem cyclRadius_pow_totient (k : ℕ) :
    cyclRadius p (k + 1) ^ Nat.totient (p ^ (k + 1)) = (p : ℝ)⁻¹ := by
  rw [← norm_sub_one_eq_cyclRadius (exists_isPrimitiveRoot (p := p) (k + 1)).choose_spec]
  exact norm_sub_one_pow_totient (exists_isPrimitiveRoot (p := p) (k + 1)).choose_spec

theorem cyclRadius_le_one (j : ℕ) : cyclRadius p j ≤ 1 :=
  norm_sub_one_le_one (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
    (exists_isPrimitiveRoot (p := p) j).choose_spec.pow_eq_one

theorem inv_p_le_cyclRadius (k : ℕ) : (p : ℝ)⁻¹ ≤ cyclRadius p (k + 1) := by
  rw [← cyclRadius_pow_totient k]
  exact pow_le_of_le_one (norm_nonneg _) (cyclRadius_le_one _)
    (Nat.totient_pos.2 (pow_pos (Fact.out : p.Prime).pos _)).ne'

theorem cyclRadius_pos (k : ℕ) : 0 < cyclRadius p (k + 1) :=
  lt_of_lt_of_le (inv_pos.2 (by exact_mod_cast (Fact.out : p.Prime).pos)) (inv_p_le_cyclRadius k)

theorem cyclRadius_succ_pow {k : ℕ} (hk : 1 ≤ k) : cyclRadius p (k + 1) ^ p = cyclRadius p k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hφ : Nat.totient (p ^ (j + 1)) ≠ 0 :=
    (Nat.totient_pos.2 (pow_pos (Fact.out : p.Prime).pos _)).ne'
  refine (pow_left_inj₀ (pow_nonneg (cyclRadius_nonneg (p := p) _) _) (cyclRadius_nonneg (p := p) _)
    hφ).1 ?_
  rw [← pow_mul, ← totient_prime_pow_succ (p := p) (k := j + 1) (by omega),
    cyclRadius_pow_totient (p := p) (j + 1), cyclRadius_pow_totient (p := p) j]

theorem cyclRadius_succ_pow_pred {k : ℕ} (hk : 1 ≤ k) :
    cyclRadius p (k + 1) ^ (p - 1) = cyclRadius p k / cyclRadius p (k + 1) := by
  have hp : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have h : cyclRadius p (k + 1) ^ (p - 1) * cyclRadius p (k + 1) = cyclRadius p k := by
    rw [← pow_succ, Nat.sub_add_cancel hp, cyclRadius_succ_pow (p := p) hk]
  rw [eq_div_iff (cyclRadius_pos (p := p) k).ne', h]

theorem adjoin_sub_one_eq_cycl {ζ : PadicAlgCl p} {n : ℕ} (hζ : IsPrimitiveRoot ζ (p ^ n)) :
    ℚ_[p]⟮ζ - 1⟯ = cycl p n := by
  rw [cycl_eq_adjoin hζ]
  apply le_antisymm
  · rw [adjoin_simple_le_iff]
    exact sub_mem (mem_adjoin_simple_self ℚ_[p] ζ) (one_mem _)
  · rw [adjoin_simple_le_iff]
    have h := add_mem (mem_adjoin_simple_self ℚ_[p] (ζ - 1)) (one_mem ℚ_[p]⟮ζ - 1⟯)
    rwa [sub_add_cancel] at h

theorem exists_eq_sum_pow_of_adjoin_eq {k : ℕ} (hk : 1 ≤ k) {y : PadicAlgCl p}
    (hy : ℚ_[p]⟮y⟯ = cycl p (k + 1)) {x : PadicAlgCl p} (hx : x ∈ cycl p (k + 1)) :
    ∃ b : ℕ → PadicAlgCl p, (∀ i, b i ∈ cycl p k) ∧ x = ∑ i ∈ Finset.range p, b i * y ^ i := by
  have hint : IsIntegral (cycl p k) y :=
    (Algebra.IsIntegral.isIntegral (R := ℚ_[p]) y).tower_top
  set pb := IntermediateField.adjoin.powerBasis hint
  have hdim : pb.dim = p := by
    rw [IntermediateField.adjoin.powerBasis_dim, natDegree_minpoly_cycl_of_adjoin_eq hk hy]
  have hx' : x ∈ (cycl p k)⟮y⟯ := by
    have : cycl p (k + 1) ≤ ((cycl p k)⟮y⟯).restrictScalars ℚ_[p] := by
      rw [← hy, adjoin_simple_le_iff, mem_restrictScalars]
      exact mem_adjoin_simple_self _ y
    exact this hx
  obtain ⟨f, hfdeg, hf⟩ := pb.exists_eq_aeval ⟨x, hx'⟩
  refine ⟨fun i => algebraMap (cycl p k) (PadicAlgCl p) (f.coeff i), fun i => (f.coeff i).2, ?_⟩
  have h1 : x = aeval y f := by
    have := congrArg (algebraMap ((cycl p k)⟮y⟯) (PadicAlgCl p)) hf
    rw [IntermediateField.adjoin.powerBasis_gen, ← aeval_algebraMap_apply] at this
    exact this
  rw [h1, aeval_eq_sum_range' (hfdeg.trans_eq hdim)]
  exact Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def]

theorem norm_mul_pow_le_norm_sum {k : ℕ} (hk : 1 ≤ k) {ζ : PadicAlgCl p}
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) {b : ℕ → PadicAlgCl p} (hb : ∀ i, b i ∈ cycl p k) :
    ∀ i ∈ Finset.range p, ‖b i‖ * ‖ζ - 1‖ ^ i ≤ ‖∑ i ∈ Finset.range p, b i * (ζ - 1) ^ i‖ := by
  set π := ζ - 1
  set x := ∑ i ∈ Finset.range p, b i * π ^ i
  set φ := Nat.totient (p ^ k)
  have hπpow : ‖π‖ ^ (p * φ) = (p : ℝ)⁻¹ := by
    rw [← totient_prime_pow_succ hk]; exact norm_sub_one_pow_totient hζ

  have hterm : ∀ i, b i ≠ 0 → ∃ z : ℤ, (‖b i‖ * ‖π‖ ^ i) ^ (p * φ) = (p : ℝ) ^ ((p : ℤ) * z - i) := by
    intro i hi
    obtain ⟨z, hz⟩ := exists_norm_pow_totient_eq_zpow (hb i) hi
    refine ⟨z, ?_⟩
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    calc (‖b i‖ * ‖π‖ ^ i) ^ (p * φ) = (‖b i‖ ^ φ) ^ p * (‖π‖ ^ (p * φ)) ^ i := by ring
      _ = ((p : ℝ) ^ z) ^ p * ((p : ℝ)⁻¹) ^ i := by rw [hz, hπpow]
      _ = (p : ℝ) ^ ((p : ℤ) * z - i) := by
        rw [← zpow_natCast ((p : ℝ) ^ z) p, ← zpow_mul, inv_pow, ← zpow_natCast (p : ℝ) i,
          ← zpow_neg, ← zpow_add₀ hp0]
        congr 1; ring
  have hdistinct : ∀ i ∈ Finset.range p, ∀ j ∈ Finset.range p, i ≠ j → b i ≠ 0 → b j ≠ 0 →
      ‖b i‖ * ‖π‖ ^ i ≠ ‖b j‖ * ‖π‖ ^ j := by
    intro i hi j hj hij hbi hbj h
    obtain ⟨zi, hzi⟩ := hterm i hbi
    obtain ⟨zj, hzj⟩ := hterm j hbj
    have := zpow_p_injective (p := p) (hzi.symm.trans ((congrArg (· ^ (p * φ)) h).trans hzj))
    have hi' := Finset.mem_range.1 hi
    have hj' := Finset.mem_range.1 hj
    have hdvd : (p : ℤ) ∣ ((i : ℤ) - j) := ⟨zi - zj, by linear_combination (-1 : ℤ) * this⟩
    have habs : |(i : ℤ) - j| < p := by rw [abs_lt]; constructor <;> omega
    exact hij (by have := Int.eq_zero_of_abs_lt_dvd hdvd habs; omega)
  intro i hi
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨i0, hi0, hmax⟩ := Finset.exists_max_image (Finset.range p) (fun i => ‖b i‖ * ‖π‖ ^ i)
    ⟨i, hi⟩
  set M := ‖b i0‖ * ‖π‖ ^ i0
  have hxM : ‖x‖ < M := lt_of_lt_of_le hlt (hmax i hi)
  have hM0 : 0 < M := lt_of_le_of_lt (norm_nonneg _) hxM
  have hbi0 : b i0 ≠ 0 := by
    intro h; rw [show M = 0 by simp [M, h]] at hM0; exact lt_irrefl 0 hM0
  have hlt' : ∀ j ∈ (Finset.range p).erase i0, ‖b j * π ^ j‖ < M := by
    intro j hj
    rw [norm_mul, norm_pow]
    rcases eq_or_ne (b j) 0 with h | h
    · rw [h, norm_zero, zero_mul]; exact hM0
    · exact lt_of_le_of_ne (hmax j (Finset.mem_of_mem_erase hj))
        (hdistinct j (Finset.mem_of_mem_erase hj) i0 hi0 (Finset.ne_of_mem_erase hj) h hbi0)
  set rest := ∑ j ∈ (Finset.range p).erase i0, b j * π ^ j
  have hrest : ‖rest‖ < M := by
    rcases ((Finset.range p).erase i0).eq_empty_or_nonempty with h | h
    · rw [show rest = 0 by simp [rest, h], norm_zero]; exact hM0
    · obtain ⟨j, hj, hjle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty h
        (fun j => b j * π ^ j)
      exact lt_of_le_of_lt hjle (hlt' j hj)
  have hx : x = b i0 * π ^ i0 + rest := (Finset.add_sum_erase _ _ hi0).symm
  have : ‖b i0 * π ^ i0‖ ≤ max ‖x‖ ‖rest‖ := by
    have h1 := IsUltrametricDist.norm_add_le_max x (-rest)
    rw [norm_neg] at h1
    calc ‖b i0 * π ^ i0‖ = ‖x + -rest‖ := by rw [hx, add_neg_cancel_right]
      _ ≤ max ‖x‖ ‖rest‖ := h1
  rw [norm_mul, norm_pow] at this
  exact absurd this (not_le.2 (max_lt hxM hrest))

theorem normTrace_cycl_sub_one_pow {k : ℕ} (hk : 1 ≤ k) {ζ : PadicAlgCl p}
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) {i : ℕ} (hi : i < p) :
    normTrace (cycl p k) ((ζ - 1) ^ i) = (-1) ^ i := by
  have hpr := (Fact.out : p.Prime)
  rw [sub_eq_add_neg, add_pow, normTrace_sum]
  rw [Finset.sum_eq_single 0]
  · simp only [pow_zero, one_mul, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
    exact normTrace_of_mem _ (pow_mem (neg_mem (one_mem _)) _)
  · intro j hj hj0
    have hjp : j < p := lt_of_lt_of_le (Finset.mem_range.1 hj) (by omega)
    have hmem : (-1 : PadicAlgCl p) ^ (i - j) * (i.choose j : PadicAlgCl p) ∈ cycl p k :=
      mul_mem (pow_mem (neg_mem (one_mem _)) _) (IntermediateField.natCast_mem _ _)
    rw [mul_assoc, mul_comm, normTrace_mul_of_mem _ hmem]
    have hcop : j.Coprime (p ^ (k + 1)) :=
      Nat.Coprime.pow_right _ (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hpr).2
        fun h => by have := Nat.le_of_dvd (by omega) h; omega))
    rw [normTrace_cycl_isPrimitiveRoot hk (hζ.pow_of_coprime j hcop), mul_zero]
  · intro h; exact absurd (Finset.mem_range.2 (Nat.succ_pos i)) h

theorem norm_normTrace_cycl_succ_mul_le {k : ℕ} (hk : 1 ≤ k) {x : PadicAlgCl p}
    (hx : x ∈ cycl p (k + 1)) :
    ‖normTrace (cycl p k) x‖ * cyclRadius p (k + 1) ^ (p - 1) ≤ ‖x‖ := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot (p := p) (k + 1)
  obtain ⟨b, hb, rfl⟩ := exists_eq_sum_pow_of_adjoin_eq hk (adjoin_sub_one_eq_cycl hζ) hx
  have horth := norm_mul_pow_le_norm_sum hk hζ hb
  set x := ∑ i ∈ Finset.range p, b i * (ζ - 1) ^ i
  have hr := cyclRadius_pos (p := p) k
  have hrpow : 0 < cyclRadius p (k + 1) ^ (p - 1) := pow_pos hr _
  have hrad : ‖ζ - 1‖ = cyclRadius p (k + 1) := norm_sub_one_eq_cyclRadius hζ
  have htr : normTrace (cycl p k) x = ∑ i ∈ Finset.range p, b i * (-1) ^ i := by
    rw [normTrace_sum]
    exact Finset.sum_congr rfl fun i hi => by
      rw [normTrace_mul_of_mem _ (hb i), normTrace_cycl_sub_one_pow hk hζ (Finset.mem_range.1 hi)]
  rw [htr, ← le_div_iff₀ hrpow]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (div_nonneg (norm_nonneg _) hrpow.le) fun i hi => ?_
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one, le_div_iff₀ hrpow]
  calc ‖b i‖ * cyclRadius p (k + 1) ^ (p - 1) ≤ ‖b i‖ * ‖ζ - 1‖ ^ i := by
        rw [hrad]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr.le (cyclRadius_le_one _)
          (by have := Finset.mem_range.1 hi; omega)) (norm_nonneg _)
    _ ≤ ‖x‖ := horth i hi

theorem norm_normTrace_cycl_mul_le {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) {x : PadicAlgCl p}
    (hx : x ∈ cycl p m) :
    ‖normTrace (cycl p n) x‖ * cyclRadius p n ≤ ‖x‖ * cyclRadius p m := by
  induction m, hnm using Nat.le_induction generalizing x with
  | base => rw [normTrace_of_mem _ hx]
  | succ m hnm ih =>
    have hm : 1 ≤ m := le_trans hn hnm
    rw [← normTrace_normTrace_of_le (cycl_mono hnm) x]
    have h1 := ih (normTrace_mem (cycl p m) x)
    have h2 := norm_normTrace_cycl_succ_mul_le hm hx
    rw [cyclRadius_succ_pow_pred hm, mul_div_assoc', div_le_iff₀ (cyclRadius_pos (p := p) m)] at h2
    exact h1.trans h2

theorem norm_normTrace_cycl_le {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) {x : PadicAlgCl p}
    (hx : x ∈ cycl p m) : ‖normTrace (cycl p n) x‖ ≤ p * ‖x‖ := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  have h := norm_normTrace_cycl_mul_le hn hnm hx
  have hr := cyclRadius_pos (p := p) j
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have h1 : ‖normTrace (cycl p (j + 1)) x‖ * cyclRadius p (j + 1) ≤ ‖x‖ :=
    h.trans (mul_le_of_le_one_right (norm_nonneg _) (cyclRadius_le_one _))
  have h2 : (p : ℝ)⁻¹ ≤ cyclRadius p (j + 1) := inv_p_le_cyclRadius j
  calc ‖normTrace (cycl p (j + 1)) x‖ = p * (‖normTrace (cycl p (j + 1)) x‖ * (p : ℝ)⁻¹) := by
        field_simp
    _ ≤ p * (‖normTrace (cycl p (j + 1)) x‖ * cyclRadius p (j + 1)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (norm_nonneg _)) hp0.le
    _ ≤ p * ‖x‖ := mul_le_mul_of_nonneg_left h1 hp0.le

end

end GroundTheory.PAdicHodge
end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.PAdicHodge.CyclotomicTower =====

-- ===== clump member: GroundTheory.PAdicHodge.TateNormalizedTrace =====
-- clump-header: {"m": "GroundTheory.PAdicHodge.TateNormalizedTrace", "h": "module\n\npublic import GroundTheory.PAdicHodge.NormalizedTraceTower\npublic import GroundTheory.PAdicHodge.NormalizedTraceClosure\npublic import GroundTheory.PAdicHodge.CyclotomicTower\nimport GroundTheory.PAdicHodge.GaloisOnCp\nimport Mathlib.Algebra.Lie.OfAssociative\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Connected.Separation\nimport Mathlib.Topology.MetricSpace.Ultra.TotallySeparated\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

open IntermediateField Module Set

noncomputable section

variable {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
  [FiniteDimensional ℚ_[p] K]

def tateTrace (n : ℕ) : PadicAlgCl p → PadicAlgCl p := normTrace (cyclotomicLayer K n)

theorem tateTrace_add (n : ℕ) (y z : PadicAlgCl p) :
    tateTrace K n (y + z) = tateTrace K n y + tateTrace K n z :=
  normTrace_add _ y z

theorem tateTrace_mem (n : ℕ) (y : PadicAlgCl p) : tateTrace K n y ∈ cyclotomicLayer K n :=
  normTrace_mem _ y

theorem tateTrace_of_mem {n : ℕ} {a : PadicAlgCl p} (ha : a ∈ cyclotomicLayer K n) :
    tateTrace K n a = a :=
  normTrace_of_mem _ ha

theorem tateTrace_mul_of_mem {n : ℕ} {a : PadicAlgCl p} (ha : a ∈ cyclotomicLayer K n)
    (y : PadicAlgCl p) : tateTrace K n (a * y) = a * tateTrace K n y :=
  normTrace_mul_of_mem _ ha y

theorem tateTrace_gal (σ : Gal(PadicAlgCl p/K)) (n : ℕ) (y : PadicAlgCl p) :
    tateTrace K n (σ y) = σ (tateTrace K n y) :=
  normTrace_cyclotomicLayer_gal K σ n y

theorem tateTrace_tateTrace_of_le {n n' : ℕ} (h : n ≤ n') (y : PadicAlgCl p) :
    tateTrace K n (tateTrace K n' y) = tateTrace K n y :=
  normTrace_normTrace_of_le (cyclotomicLayer_mono K h) y

theorem exists_norm_tateTrace_le_of_stableIndex_le :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ n, stableIndex K ≤ n → ∀ x ∈ cyclotomicLimit K,
      ‖tateTrace K n x‖ ≤ c * ‖x‖ := by
  refine ⟨p * ∑ i, ‖towerVec K i‖ * ‖towerDualVec K i‖,
    mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)), ?_⟩
  intro n hn x hx
  obtain ⟨m, hm⟩ := (mem_cyclotomicLimit K).1 hx
  have hm' : x ∈ cyclotomicLayer K (max m n) := cyclotomicLayer_mono K (le_max_left m n) hm
  refine norm_normTrace_cyclotomicLayer_le K (Nat.cast_nonneg p) ?_ hn (le_max_right m n) hm'
  intro n' m' hn' hnm' y hy
  exact norm_normTrace_cycl_le
    (le_trans (by norm_num) ((two_le_stableIndex K).trans hn')) hnm' hy

theorem exists_norm_tateTrace_le_on_layer (n N : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x ∈ cyclotomicLayer K N, ‖tateTrace K n x‖ ≤ c * ‖x‖ := by
  let S : Submodule ℚ_[p] (PadicAlgCl p) := (cyclotomicLayer K N).toSubalgebra.toSubmodule
  haveI : FiniteDimensional ℚ_[p] S :=
    inferInstanceAs (FiniteDimensional ℚ_[p] (cyclotomicLayer K N))
  let f : S →ₗ[ℚ_[p]] PadicAlgCl p :=
    ((normTraceₗ (cyclotomicLayer K n)).restrictScalars ℚ_[p]).comp S.subtype
  let f' := LinearMap.toContinuousLinearMap f
  refine ⟨‖f'‖, ContinuousLinearMap.opNorm_nonneg f', fun x hx => ?_⟩
  have := f'.le_opNorm ⟨x, hx⟩
  exact this

theorem exists_norm_tateTrace_le :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ n, ∀ x ∈ cyclotomicLimit K, ‖tateTrace K n x‖ ≤ c * ‖x‖ := by
  obtain ⟨c, hc0, hc⟩ := exists_norm_tateTrace_le_of_stableIndex_le K
  choose c' hc'0 hc' using fun n => exists_norm_tateTrace_le_on_layer K n (stableIndex K)
  refine ⟨c * (1 + ∑ n ∈ Finset.range (stableIndex K), c' n), by
    have : 0 ≤ ∑ n ∈ Finset.range (stableIndex K), c' n := Finset.sum_nonneg fun n _ => hc'0 n
    positivity, ?_⟩
  intro n x hx
  have hs : 0 ≤ ∑ n ∈ Finset.range (stableIndex K), c' n := Finset.sum_nonneg fun n _ => hc'0 n
  by_cases hn : stableIndex K ≤ n
  · calc ‖tateTrace K n x‖ ≤ c * ‖x‖ := hc n hn x hx
      _ ≤ c * (1 + ∑ n ∈ Finset.range (stableIndex K), c' n) * ‖x‖ := by
        nlinarith [mul_nonneg (mul_nonneg hc0 hs) (norm_nonneg x)]
  · push Not at hn
    have hle : c' n ≤ ∑ n ∈ Finset.range (stableIndex K), c' n :=
      Finset.single_le_sum (fun n _ => hc'0 n) (Finset.mem_range.2 hn)
    rw [← tateTrace_tateTrace_of_le K hn.le x]
    calc ‖tateTrace K n (tateTrace K (stableIndex K) x)‖
        ≤ c' n * ‖tateTrace K (stableIndex K) x‖ := hc' n _ (tateTrace_mem K _ x)
      _ ≤ c' n * (c * ‖x‖) := mul_le_mul_of_nonneg_left (hc _ le_rfl x hx) (hc'0 n)
      _ ≤ c * (1 + ∑ n ∈ Finset.range (stableIndex K), c' n) * ‖x‖ := by
        have := norm_nonneg x
        nlinarith [mul_nonneg hc0 this]

def tateBound : ℝ := Classical.choose (exists_norm_tateTrace_le K)

theorem tateBound_nonneg : 0 ≤ tateBound K := (Classical.choose_spec (exists_norm_tateTrace_le K)).1

theorem norm_tateTrace_le (n : ℕ) {x : PadicAlgCl p} (hx : x ∈ cyclotomicLimit K) :
    ‖tateTrace K n x‖ ≤ tateBound K * ‖x‖ :=
  (Classical.choose_spec (exists_norm_tateTrace_le K)).2 n x hx

section Completion

def cyclotomicCompletion : Set ℂ_[p] := closureInCp (cyclotomicLimit K)

def tateTraceHat (n : ℕ) : ℂ_[p] → ℂ_[p] := extendToClosure (cyclotomicLimit K) (tateTrace K n)

variable {K}

theorem tateTrace_add_of_mem (n : ℕ) : ∀ y ∈ cyclotomicLimit K, ∀ z ∈ cyclotomicLimit K,
    tateTrace K n (y + z) = tateTrace K n y + tateTrace K n z :=
  fun y _ z _ => tateTrace_add K n y z

theorem norm_tateTrace_le_of_mem (n : ℕ) : ∀ y ∈ cyclotomicLimit K,
    ‖tateTrace K n y‖ ≤ tateBound K * ‖y‖ :=
  fun _ hy => norm_tateTrace_le K n hy

theorem norm_tateTraceHat_le (n : ℕ) {x : ℂ_[p]} (hx : x ∈ cyclotomicCompletion K) :
    ‖tateTraceHat K n x‖ ≤ tateBound K * ‖x‖ :=
  norm_extendToClosure_le (tateTrace_add_of_mem n) (norm_tateTrace_le_of_mem n) hx

theorem tateTraceHat_add (n : ℕ) {x x' : ℂ_[p]} (hx : x ∈ cyclotomicCompletion K)
    (hx' : x' ∈ cyclotomicCompletion K) :
    tateTraceHat K n (x + x') = tateTraceHat K n x + tateTraceHat K n x' :=
  (extendToClosure_add (tateTrace_add_of_mem n) (norm_tateTrace_le_of_mem n) hx hx').2

theorem tateTraceHat_mem (n : ℕ) {x : ℂ_[p]} (hx : x ∈ cyclotomicCompletion K) :
    tateTraceHat K n x ∈
      ((↑) : PadicAlgCl p → ℂ_[p]) '' (cyclotomicLayer K n : Set (PadicAlgCl p)) :=
  extendToClosure_mem (tateTrace_add_of_mem n) (norm_tateTrace_le_of_mem n)
    (fun y _ => tateTrace_mem K n y) hx

theorem tateTraceHat_coe_of_mem {n : ℕ} {a : PadicAlgCl p} (ha : a ∈ cyclotomicLayer K n) :
    tateTraceHat K n (a : ℂ_[p]) = a :=
  extendToClosure_coe_of_mem (tateTrace_add_of_mem n) (norm_tateTrace_le_of_mem n)
    (cyclotomicLayer_le_cyclotomicLimit K n) (fun a ha => tateTrace_of_mem K ha) ha

theorem tateTraceHat_mul {n : ℕ} {a : PadicAlgCl p} (ha : a ∈ cyclotomicLayer K n) {x : ℂ_[p]}
    (hx : x ∈ cyclotomicCompletion K) :
    tateTraceHat K n ((a : ℂ_[p]) * x) = (a : ℂ_[p]) * tateTraceHat K n x :=
  extendToClosure_mul (tateTrace_add_of_mem n) (norm_tateTrace_le_of_mem n)
    (cyclotomicLayer_le_cyclotomicLimit K n) (fun a ha y _ => tateTrace_mul_of_mem K ha y) ha hx

theorem gal_mem_cyclotomicLimit (σ : Gal(PadicAlgCl p/K)) {y : PadicAlgCl p}
    (hy : y ∈ cyclotomicLimit K) : σ y ∈ cyclotomicLimit K :=
  map_mem_cyclotomicLimit K (σ.restrictScalars ℚ_[p]) (fun x hx => σ.commutes ⟨x, hx⟩) hy

theorem smul_mem_cyclotomicCompletion (σ : Gal(PadicAlgCl p/K)) {x : ℂ_[p]}
    (hx : x ∈ cyclotomicCompletion K) : σ • x ∈ cyclotomicCompletion K :=
  smul_mem_closureInCp σ (fun _ hy => gal_mem_cyclotomicLimit σ hy) hx

theorem tateTraceHat_smul (n : ℕ) (σ : Gal(PadicAlgCl p/K)) {x : ℂ_[p]}
    (hx : x ∈ cyclotomicCompletion K) : tateTraceHat K n (σ • x) = σ • tateTraceHat K n x :=
  extendToClosure_smul (tateTrace_add_of_mem n) (norm_tateTrace_le_of_mem n) σ
    (fun _ hy => gal_mem_cyclotomicLimit σ hy) (fun y _ => tateTrace_gal K σ n y) hx

end Completion

section Gamma

variable {K}

end Gamma

end

end GroundTheory.PAdicHodge
end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.PAdicHodge.TateNormalizedTrace =====

-- ===== clump member: GroundTheory.PAdicHodge.ExistsGalFixCyclotomicLayerCycloCharNeOne =====
-- clump-header: {"m": "GroundTheory.PAdicHodge.ExistsGalFixCyclotomicLayerCycloCharNeOne", "h": "module\n\npublic import GroundTheory.PAdicHodge.TateCpTwist\npublic import GroundTheory.PAdicHodge.TateNormalizedTrace\npublic import GroundTheory.PAdicHodge.AxLemma\nimport GroundTheory.PAdicHodge.CyclotomicTower\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Int\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

open IntermediateField UniformSpace

variable {p : ℕ} [hp : Fact p.Prime]

section Torsion

theorem one_add_pow_ne_one {w : PadicAlgCl p} (hw0 : w ≠ 0) (hw : ‖w‖ < (p : ℝ)⁻¹) {m : ℕ}
    (hm : m ≠ 0) : (1 + w) ^ m ≠ 1 := by
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  have hexp : (1 + w) ^ (m' + 1) - 1 = ((m' + 1 : ℕ) : PadicAlgCl p) * w +
      ∑ k ∈ Finset.range m', w ^ (k + 1 + 1) * ((m' + 1).choose (k + 1 + 1) : PadicAlgCl p) := by
    rw [add_comm (1 : PadicAlgCl p) w, add_pow, Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one, pow_one,
      Nat.choose_one_right, zero_add]
    ring
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
  have hmpos : 0 < ‖((m' + 1 : ℕ) : PadicAlgCl p)‖ := by
    rw [norm_pos_iff]; exact_mod_cast Nat.succ_ne_zero m'
  have hlead : 0 < ‖((m' + 1 : ℕ) : PadicAlgCl p) * w‖ := by
    rw [norm_mul]; exact mul_pos hmpos hwpos

  have hterm : ∀ k ∈ Finset.range m', ‖w ^ (k + 1 + 1) * ((m' + 1).choose (k + 1 + 1) : PadicAlgCl p)‖
      < ‖((m' + 1 : ℕ) : PadicAlgCl p) * w‖ := by
    intro k _

    have hch : ((m' + 1).choose (k + 1 + 1) : PadicAlgCl p) * ((k + 1 + 1 : ℕ) : PadicAlgCl p) =
        ((m' + 1 : ℕ) : PadicAlgCl p) * (m'.choose (k + 1) : PadicAlgCl p) := by
      exact_mod_cast (Nat.add_one_mul_choose_eq m' (k + 1)).symm
    have hk0 : (k + 1 + 1 : ℕ) ≠ 0 := by omega
    have hknorm : ((k + 1 + 1 : ℕ) : ℝ)⁻¹ ≤ ‖((k + 1 + 1 : ℕ) : PadicAlgCl p)‖ := by
      rw [norm_natCast_padicAlgCl hk0, zpow_neg, zpow_natCast]
      gcongr
      exact_mod_cast Nat.le_of_dvd (by omega) (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))
    have hkpos : (0 : ℝ) < ((k + 1 + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
    have hC : ‖((m' + 1).choose (k + 1 + 1) : PadicAlgCl p)‖ ≤
        ‖((m' + 1 : ℕ) : PadicAlgCl p)‖ * ((k + 1 + 1 : ℕ) : ℝ) := by
      have h1 := congrArg norm hch
      rw [norm_mul, norm_mul] at h1
      have h2 : ‖(m'.choose (k + 1) : PadicAlgCl p)‖ ≤ 1 :=
        IsUltrametricDist.norm_natCast_le_one (PadicAlgCl p) _
      have h3 : ‖((m' + 1).choose (k + 1 + 1) : PadicAlgCl p)‖ * ((k + 1 + 1 : ℕ) : ℝ)⁻¹ ≤
          ‖((m' + 1 : ℕ) : PadicAlgCl p)‖ := by
        calc _ ≤ ‖((m' + 1).choose (k + 1 + 1) : PadicAlgCl p)‖ *
              ‖((k + 1 + 1 : ℕ) : PadicAlgCl p)‖ := by gcongr
          _ = _ := h1
          _ ≤ ‖((m' + 1 : ℕ) : PadicAlgCl p)‖ * 1 := by gcongr
          _ = _ := mul_one _
      rwa [← div_eq_mul_inv, div_le_iff₀ hkpos] at h3

    have hpow : ((k + 1 + 1 : ℕ) : ℝ) * ‖w‖ ^ (k + 1) < 1 := by
      have h1 : ‖w‖ ^ (k + 1) < ((p : ℝ)⁻¹) ^ (k + 1) :=
        pow_lt_pow_left₀ hw (norm_nonneg _) (Nat.succ_ne_zero k)
      have h2 : ((k + 1 + 1 : ℕ) : ℝ) ≤ (p : ℝ) ^ (k + 1) := by
        have := Nat.lt_pow_self (n := k + 1) hp.out.one_lt
        exact_mod_cast this
      calc ((k + 1 + 1 : ℕ) : ℝ) * ‖w‖ ^ (k + 1) < ((k + 1 + 1 : ℕ) : ℝ) * ((p : ℝ)⁻¹) ^ (k + 1) :=
            mul_lt_mul_of_pos_left h1 hkpos
        _ ≤ (p : ℝ) ^ (k + 1) * ((p : ℝ)⁻¹) ^ (k + 1) := by gcongr
        _ = 1 := by rw [← mul_pow, mul_inv_cancel₀ (by positivity), one_pow]
    rw [norm_mul, norm_pow, norm_mul]
    calc ‖w‖ ^ (k + 1 + 1) * ‖((m' + 1).choose (k + 1 + 1) : PadicAlgCl p)‖
        ≤ ‖w‖ ^ (k + 1 + 1) * (‖((m' + 1 : ℕ) : PadicAlgCl p)‖ * ((k + 1 + 1 : ℕ) : ℝ)) := by
          gcongr
      _ = (‖((m' + 1 : ℕ) : PadicAlgCl p)‖ * ‖w‖) * (((k + 1 + 1 : ℕ) : ℝ) * ‖w‖ ^ (k + 1)) := by
          ring
      _ < (‖((m' + 1 : ℕ) : PadicAlgCl p)‖ * ‖w‖) * 1 :=
          mul_lt_mul_of_pos_left hpow (mul_pos hmpos hwpos)
      _ = _ := mul_one _
  have htail : ‖∑ k ∈ Finset.range m', w ^ (k + 1 + 1) * ((m' + 1).choose (k + 1 + 1) : PadicAlgCl p)‖
      < ‖((m' + 1 : ℕ) : PadicAlgCl p) * w‖ := by
    rcases (Finset.range m').eq_empty_or_nonempty with h | h
    · rw [h, Finset.sum_empty, norm_zero]; exact hlead
    · obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty h
        (fun k => w ^ (k + 1 + 1) * ((m' + 1).choose (k + 1 + 1) : PadicAlgCl p))
      exact hle.trans_lt (hterm i hi)
  intro h
  have h0 : (1 + w) ^ (m' + 1) - 1 = 0 := by rw [h, sub_self]
  rw [hexp] at h0
  have hne : ‖((m' + 1 : ℕ) : PadicAlgCl p) * w‖ ≠
      ‖∑ k ∈ Finset.range m', w ^ (k + 1 + 1) * ((m' + 1).choose (k + 1 + 1) : PadicAlgCl p)‖ :=
    htail.ne'
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
  rw [h0, norm_zero] at this
  exact hlead.ne (this.trans (max_eq_left htail.le))

end Torsion

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

section Character

theorem cycloChar_toZModPow_eq_one (σ : Gal(PadicAlgCl p/K)) (n : ℕ)
    (h : ∀ ζ : PadicAlgCl p, ζ ^ p ^ n = 1 → σ ζ = ζ) :
    (cycloChar K σ : ℤ_[p]).toZModPow n = 1 := by
  rw [cycloChar, MonoidHom.comp_apply, cyclotomicCharacter.toZModPow]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact @Subsingleton.elim (ZMod 1) _ _ _
  refine (modularCyclotomicCharacter.unique _ _ _ ?_).symm
  intro t ht
  have hp1 : p ^ n ≠ 1 := (Nat.one_lt_pow hn.ne' hp.out.one_lt).ne'
  rw [ZMod.val_one'' hp1, pow_one]
  have ht' : (t : PadicAlgCl p) ^ p ^ n = 1 := by
    have := (mem_rootsOfUnity _ _).1 ht
    simpa using congrArg Units.val this
  exact h _ ht'

theorem norm_cycloChar_sub_one_le (σ : Gal(PadicAlgCl p/K)) (n : ℕ)
    (h : ∀ ζ : PadicAlgCl p, ζ ^ p ^ n = 1 → σ ζ = ζ) :
    ‖(cycloChar K σ : ℤ_[p]) - 1‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub,
    map_one, cycloChar_toZModPow_eq_one K σ n h, sub_self]

theorem cycloChar_eq_one_of_forall (σ : Gal(PadicAlgCl p/K))
    (h : ∀ n : ℕ, ∀ ζ : PadicAlgCl p, ζ ^ p ^ n = 1 → σ ζ = ζ) : cycloChar K σ = 1 := by
  refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
  rw [cycloChar_toZModPow_eq_one K σ n (h n), Units.val_one, map_one]

theorem cycloChar_zpow_ne_one (σ : Gal(PadicAlgCl p/K))
    (h2 : ∀ ζ : PadicAlgCl p, ζ ^ p ^ 2 = 1 → σ ζ = ζ) (hne : cycloChar K σ ≠ 1) {j : ℤ}
    (hj : j ≠ 0) : cycloChar K σ ^ j ≠ 1 := by
  intro hpow
  have hm : cycloChar K σ ^ j.natAbs = 1 := by
    rcases Int.natAbs_eq j with hj' | hj'
    · rw [hj', zpow_natCast] at hpow; exact hpow
    · rw [hj', zpow_neg, inv_eq_one, zpow_natCast] at hpow; exact hpow
  set u : ℤ_[p] := ((cycloChar K σ : ℤ_[p]ˣ) : ℤ_[p])
  set w : PadicAlgCl p := algebraMap ℚ_[p] (PadicAlgCl p) ((u - 1 : ℤ_[p]) : ℚ_[p])
  have hw0 : w ≠ 0 := by
    intro hw
    rw [map_eq_zero, PadicInt.coe_eq_zero, sub_eq_zero] at hw
    exact hne (Units.ext hw)
  have hw : ‖w‖ < (p : ℝ)⁻¹ := by
    rw [norm_algebraMap', ← PadicInt.norm_def]
    refine (norm_cycloChar_sub_one_le K σ 2 h2).trans_lt ?_
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
    rw [← zpow_neg_one]
    exact zpow_lt_zpow_right₀ hp1 (by norm_num)
  apply one_add_pow_ne_one hw0 hw (Int.natAbs_ne_zero.2 hj)
  have h1 : (1 : PadicAlgCl p) + w = algebraMap ℚ_[p] (PadicAlgCl p) (u : ℚ_[p]) := by
    simp [w, u]
  rw [h1, ← map_pow, ← PadicInt.coe_pow, ← Units.val_pow_eq_pow_val, hm]
  simp

theorem twistScalar_ne_one (σ : Gal(PadicAlgCl p/K))
    (h2 : ∀ ζ : PadicAlgCl p, ζ ^ p ^ 2 = 1 → σ ζ = ζ) (hne : cycloChar K σ ≠ 1) {j : ℤ}
    (hj : j ≠ 0) : twistScalar K j σ ≠ 1 := by
  intro h
  rw [twistScalar, ← map_one (algebraMap ℚ_[p] ℂ_[p]),
    (algebraMap ℚ_[p] ℂ_[p]).injective.eq_iff] at h
  have h' : ((cycloChar K σ ^ j : ℤ_[p]ˣ) : ℤ_[p]) = 1 := Subtype.ext h
  exact cycloChar_zpow_ne_one K σ h2 hne hj (Units.ext h')

variable [FiniteDimensional ℚ_[p] K]

theorem exists_gal_fix_cyclotomicLayer_cycloChar_ne_one (n : ℕ) :
    ∃ σ : Gal(PadicAlgCl p/K), (∀ y ∈ cyclotomicLayer K n, σ y = y) ∧ cycloChar K σ ≠ 1 := by
  by_contra hcon
  push Not at hcon
  set E : IntermediateField K (PadicAlgCl p) := extendScalars (le_cyclotomicLayer K n)
  have hcyc : ∀ m, cycl p m ≤ cyclotomicLayer K n := by
    intro m
    refine adjoin_le_iff.2 fun ζ hζ => ?_
    have hζ' : ζ ^ p ^ m = 1 := hζ
    have hmem : ζ ∈ fixedField E.fixingSubgroup := by
      rw [mem_fixedField_iff]
      intro σ hσ
      have hσ' : ∀ y ∈ cyclotomicLayer K n, σ y = y := fun y hy =>
        (mem_fixingSubgroup_iff _ _).1 hσ y hy
      have h1 := hcon σ hσ'
      rw [cycloChar_spec K σ hζ', h1, Units.val_one, map_one]
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp only [pow_zero, pow_one] at hζ'
        simp [hζ']
      · have hp1 : p ^ m ≠ 1 := (Nat.one_lt_pow hm.ne' hp.out.one_lt).ne'
        rw [ZMod.val_one'' hp1, pow_one]
    rw [InfiniteGalois.fixedField_fixingSubgroup] at hmem
    exact hmem
  have hle := IntermediateField.finrank_le_of_le_right (hcyc (Module.finrank ℚ_[p] (cyclotomicLayer K n) + 1))
  rw [finrank_cycl, Nat.totient_prime_pow_succ hp.out] at hle
  have h1 : Module.finrank ℚ_[p] (cyclotomicLayer K n) < p ^ Module.finrank ℚ_[p] (cyclotomicLayer K n) :=
    Nat.lt_pow_self hp.out.one_lt
  have h2 : 1 ≤ p - 1 := by have := hp.out.two_le; omega
  have h3 : p ^ Module.finrank ℚ_[p] (cyclotomicLayer K n) ≤
      p ^ Module.finrank ℚ_[p] (cyclotomicLayer K n) * (p - 1) := Nat.le_mul_of_pos_right _ h2
  omega

end Character

section Invariants

noncomputable abbrev cyclotomicLimitGal : Subgroup Gal(PadicAlgCl p/K) :=
  (extendScalars ((le_cyclotomicLayer K 0).trans (cyclotomicLayer_le_cyclotomicLimit K 0))).fixingSubgroup

theorem cycloChar_eq_one_of_mem_cyclotomicLimitGal {σ : Gal(PadicAlgCl p/K)}
    (hσ : σ ∈ cyclotomicLimitGal K) : cycloChar K σ = 1 := by
  refine cycloChar_eq_one_of_forall K σ fun n ζ hζ => ?_
  have hmem : ζ ∈ cyclotomicLimit K :=
    cyclotomicLayer_le_cyclotomicLimit K n (cycl_le_cyclotomicLayer K n (pow_eq_one_mem_cycl hζ))
  exact (mem_fixingSubgroup_iff _ _).1 hσ ζ hmem

theorem mem_cyclotomicCompletion_of_forall_smul_eq {x : ℂ_[p]}
    (hx : ∀ σ ∈ cyclotomicLimitGal K, σ • x = x) : x ∈ cyclotomicCompletion K := by
  have h := fixedPoints_closedSubgroup_eq_closure (cyclotomicLimitGal K)
    (InfiniteGalois.fixingSubgroup_isClosed _)
  have hx' : x ∈ {x : ℂ_[p] | ∀ σ ∈ cyclotomicLimitGal K, σ • x = x} := hx
  rw [h, InfiniteGalois.fixedField_fixingSubgroup] at hx'
  exact hx'

variable [FiniteDimensional ℚ_[p] K]

theorem eq_zero_of_forall_twistScalar_mul_smul_eq {j : ℤ} (hj : j ≠ 0) {x : ℂ_[p]}
    (hx : ∀ σ : Gal(PadicAlgCl p/K), twistScalar K j σ * (σ • x) = x) : x = 0 := by

  have hxc : x ∈ cyclotomicCompletion K := by
    refine mem_cyclotomicCompletion_of_forall_smul_eq K fun σ hσ => ?_
    have h1 : twistScalar K j σ = 1 := by
      simp [twistScalar, cycloChar_eq_one_of_mem_cyclotomicLimitGal K hσ]
    simpa [h1] using hx σ

  have hR : ∀ n, stableIndex K ≤ n → tateTraceHat K n x = 0 := by
    intro n hn
    have key : ∀ σ : Gal(PadicAlgCl p/K),
        tateTraceHat K n x = twistScalar K j σ * (σ • tateTraceHat K n x) := by
      intro σ
      have hc : twistScalar K j σ =
          ((algebraMap ℚ_[p] (PadicAlgCl p) (((cycloChar K σ ^ j : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) :
            PadicAlgCl p) : ℂ_[p]) := rfl
      conv_lhs => rw [← hx σ]
      rw [hc, tateTraceHat_mul (IntermediateField.algebraMap_mem _ _) (smul_mem_cyclotomicCompletion σ hxc),
        tateTraceHat_smul n σ hxc]
    obtain ⟨σ, hσ, hne⟩ := exists_gal_fix_cyclotomicLayer_cycloChar_ne_one K n
    have h2 : ∀ ζ : PadicAlgCl p, ζ ^ p ^ 2 = 1 → σ ζ = ζ := fun ζ hζ =>
      hσ ζ (cycl_le_cyclotomicLayer K n (cycl_mono (p := p)
        ((two_le_stableIndex K).trans hn) (pow_eq_one_mem_cycl hζ)))
    obtain ⟨b, hb, hbx⟩ := tateTraceHat_mem n hxc
    have hfix : σ • tateTraceHat K n x = tateTraceHat K n x := by
      rw [← hbx, gal_smul_coe, hσ b hb]
    have h3 := key σ
    rw [hfix] at h3
    have h4 : (twistScalar K j σ - 1) * tateTraceHat K n x = 0 := by
      rw [sub_mul, one_mul, ← h3, sub_self]
    exact (mul_eq_zero.1 h4).resolve_left (sub_ne_zero.2 (twistScalar_ne_one K σ h2 hne hj))

  set c := tateBound K
  have hc0 : 0 ≤ c := tateBound_nonneg K
  have hbound : ∀ ε > 0, ‖x‖ ≤ (1 + c) * ε := by
    intro ε hε
    obtain ⟨_, ⟨y, hy, rfl⟩, hxy⟩ := Metric.mem_closure_iff.1 hxc ε hε
    obtain ⟨m, hm⟩ := (mem_cyclotomicLimit K).1 hy
    set m' := max m (stableIndex K)
    have hym : y ∈ cyclotomicLayer K m' := cyclotomicLayer_mono K (le_max_left _ _) hm
    have hyc : (y : ℂ_[p]) ∈ cyclotomicCompletion K := coe_mem_closureInCp hy
    have hsub : (y : ℂ_[p]) - x ∈ cyclotomicCompletion K := sub_mem_closureInCp hyc hxc
    have h1 : tateTraceHat K m' (y : ℂ_[p]) =
        tateTraceHat K m' ((y : ℂ_[p]) - x) + tateTraceHat K m' x := by
      rw [← tateTraceHat_add m' hsub hxc, sub_add_cancel]
    rw [tateTraceHat_coe_of_mem hym, hR m' (le_max_right _ _), add_zero] at h1
    have h2 : ‖(y : ℂ_[p])‖ ≤ c * ε := by
      rw [h1]
      refine (norm_tateTraceHat_le m' hsub).trans ?_
      rw [← dist_eq_norm, dist_comm]
      exact mul_le_mul_of_nonneg_left hxy.le hc0
    calc ‖x‖ = ‖(x - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - (y : ℂ_[p])‖ + ‖(y : ℂ_[p])‖ := norm_add_le _ _
      _ ≤ ε + c * ε := add_le_add (by rw [← dist_eq_norm]; exact hxy.le) h2
      _ = (1 + c) * ε := by ring
  by_contra hx0
  have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have h := hbound (‖x‖ / (2 * (1 + c))) (by positivity)
  have h' : (1 + c) * (‖x‖ / (2 * (1 + c))) = ‖x‖ / 2 := by
    field_simp
  rw [h'] at h
  linarith

theorem cpTwistRep_invariants_zero :
    (cpTwistRep K 0).invariants = LinearMap.range (Algebra.linearMap K ℂ_[p]) := by
  ext x
  rw [ContRepresentation.mem_invariants, LinearMap.mem_range]
  simp only [cpTwistRep_apply, twistScalar_zero, one_mul, Algebra.linearMap_apply]
  constructor
  · intro h
    obtain ⟨k, hk⟩ := exists_eq_coe_of_forall_smul_eq (K := K) h
    exact ⟨k, hk⟩
  · rintro ⟨k, rfl⟩ σ
    exact gal_smul_algebraMap_intermediateField K σ k

theorem cpTwistRep_invariants_eq_bot {j : ℤ} (hj : j ≠ 0) : (cpTwistRep K j).invariants = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [ContRepresentation.mem_invariants] at hx
  exact (Submodule.mem_bot K).2 (eq_zero_of_forall_twistScalar_mul_smul_eq K hj hx)

end Invariants

end GroundTheory.PAdicHodge
end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.PAdicHodge.ExistsGalFixCyclotomicLayerCycloCharNeOne =====
