module

public import Formalism.ConjugateSelfDual.Statement
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.VB.Cmp

variable {K Ω' : Type*} [Field K] [NumberField K] [Field Ω'] [Algebra K Ω'] (A : ValuationSubring Ω')

theorem val_le_one (x : 𝓞 K) : A.valuation (algebraMap K Ω' (x : K)) ≤ 1 := by
  have hv : A.valuation.Integers A :=
    ⟨Subtype.val_injective, fun a => A.valuation_le_one a,
      fun {r} hr => ⟨⟨r, A.mem_of_valuation_le_one r hr⟩, rfl⟩⟩
  have hx : IsIntegral ℤ (algebraMap K Ω' (x : K)) :=
    (NumberField.RingOfIntegers.isIntegral_coe x).algebraMap
  exact hv.isIntegral_iff_v_le_one.1 hx.tower_top

def ltIdeal : Ideal (𝓞 K) :=
  (IsLocalRing.maximalIdeal A).comap
    (((algebraMap K Ω').comp (algebraMap (𝓞 K) K)).codRestrict A.toSubring
      (fun x => A.mem_of_valuation_le_one _ (val_le_one A x)))

theorem mem_ltIdeal (x : 𝓞 K) : x ∈ ltIdeal (K := K) A ↔ A.valuation (algebraMap K Ω' (x : K)) < 1 :=
  A.valuation_lt_one_iff _

private theorem exists_placeOver_of_valuation_natCast_lt_one (n : ℕ) (hn : 0 < n) (h : A.valuation (n : Ω') < 1) :
    ∃ v : HeightOneSpectrum (𝓞 K), Formalism.ConjugateSelfDual.IsPlaceOver A v ∧
      ∀ x : 𝓞 K, x ∈ v.asIdeal ↔ A.valuation (algebraMap K Ω' (x : K)) < 1 := by
  have hprime : (ltIdeal (K := K) A).IsPrime := Ideal.comap_isPrime _ _
  have hmem : ((n : ℕ) : 𝓞 K) ∈ ltIdeal (K := K) A := by
    rw [mem_ltIdeal]
    simpa using h
  have hne : ((n : ℕ) : 𝓞 K) ≠ 0 := by exact_mod_cast hn.ne'
  refine ⟨⟨ltIdeal (K := K) A, hprime, fun hbot => hne (Ideal.mem_bot.1 (hbot ▸ hmem))⟩,
    fun x => (mem_ltIdeal A x).symm, fun x => mem_ltIdeal A x⟩

theorem exists_over_above_iff (l : ℕ) [Fact l.Prime] :
    (∃ v : HeightOneSpectrum (𝓞 K), Formalism.ConjugateSelfDual.IsPlaceOver A v ∧ ((l : ℕ) : 𝓞 K) ∈ v.asIdeal) ↔
      A.valuation (l : Ω') < 1 := by
  constructor
  · rintro ⟨v, hv, hl⟩
    have h := (hv _).2 hl
    simpa using h
  · intro h
    obtain ⟨v, hv, hmem⟩ := exists_placeOver_of_valuation_natCast_lt_one (K := K) A l (Fact.out : l.Prime).pos h
    exact ⟨v, hv, (hmem _).2 (by simpa using h)⟩

end Formalism.VB.Cmp
