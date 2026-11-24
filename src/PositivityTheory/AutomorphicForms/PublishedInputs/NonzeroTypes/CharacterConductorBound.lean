module

public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroLeviEigenvectorExists
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.CharacterConductor, PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.CharacterConductorBound

-- ===== clump member: PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.CharacterConductor =====
-- clump-header: {"m": "PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.CharacterConductor", "h": "module\n\npublic import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroLeviEigenvectorExists\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

namespace Grp

namespace CharacterConductor

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def CS (ψ : 𝒪[k]ˣ →* ℂˣ) : Set ℕ :=
  {c | ∀ u : 𝒪[k]ˣ, (u : 𝒪[k]) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ c → ψ u = 1}

theorem cond_eq (ψ : 𝒪[k]ˣ →* ℂˣ) : cond ψ = sInf (CS ψ) := rfl

theorem CS_mono (ψ : 𝒪[k]ˣ →* ℂˣ) {c d : ℕ} (hc : c ∈ CS ψ) (hcd : c ≤ d) : d ∈ CS ψ := by
  intro u hu
  exact hc u (Ideal.pow_le_pow_right hcd hu)

theorem CS_inv (ψ : 𝒪[k]ˣ →* ℂˣ) : CS ψ⁻¹ = CS ψ := by
  ext c
  simp only [CS, Set.mem_setOf_eq, MonoidHom.inv_apply, inv_eq_one]

theorem cond_one : cond (1 : 𝒪[k]ˣ →* ℂˣ) = 0 := by
  rw [cond_eq]
  apply Nat.sInf_eq_zero.mpr
  left
  intro u _
  rfl

theorem res_div_swap {s : ℕ} (μ : Fin s → kˣ →* ℂˣ) (a b : Fin s) :
    res (μ b / μ a) = (res (μ a / μ b))⁻¹ := by
  ext u
  simp [res, MonoidHom.div_apply, inv_div]

theorem res_div_mul {s : ℕ} (μ : Fin s → kˣ →* ℂˣ) (a b c : Fin s) (u : 𝒪[k]ˣ) :
    res (μ a / μ c) u = res (μ a / μ b) u * res (μ b / μ c) u := by
  simp [res, MonoidHom.div_apply]

theorem cc_self {s : ℕ} (μ : Fin s → kˣ →* ℂˣ) (a : Fin s) : cc μ a a = 0 := by
  unfold cc
  rw [div_self']
  exact cond_one

theorem cc_comm {s : ℕ} (μ : Fin s → kˣ →* ℂˣ) (a b : Fin s) : cc μ a b = cc μ b a := by
  unfold cc
  rw [res_div_swap μ a b, cond_eq, cond_eq, CS_inv]

theorem cc_ultra {s : ℕ} (μ : Fin s → kˣ →* ℂˣ) (a b c : Fin s)
    (hab : (CS (res (μ a / μ b))).Nonempty) (hbc : (CS (res (μ b / μ c))).Nonempty) :
    cc μ a c ≤ max (cc μ a b) (cc μ b c) := by
  have h1 : cc μ a b ∈ CS (res (μ a / μ b)) := Nat.sInf_mem hab
  have h2 : cc μ b c ∈ CS (res (μ b / μ c)) := Nat.sInf_mem hbc
  have h3 : max (cc μ a b) (cc μ b c) ∈ CS (res (μ a / μ c)) := by
    intro u hu
    rw [res_div_mul μ a b c u,
      CS_mono _ h1 (le_max_left _ _) u hu, CS_mono _ h2 (le_max_right _ _) u hu, one_mul]
  exact Nat.sInf_le h3

theorem step_ccBasic_of_cond :
    ∀ (s : ℕ) (μ : Fin s → kˣ →* ℂˣ),
      (∀ a b : Fin s, ∃ c : ℕ, ∀ u : 𝒪[k]ˣ, (u : 𝒪[k]) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ c →
        res (μ a / μ b) u = 1) →
      ∀ a b c : Fin s, cc μ a a = 0 ∧ cc μ a b = cc μ b a ∧ cc μ a c ≤ max (cc μ a b) (cc μ b c) := by
  intro s μ hμ a b c
  refine ⟨cc_self μ a, cc_comm μ a b, cc_ultra μ a b c ?_ ?_⟩
  · obtain ⟨c0, h⟩ := hμ a b
    exact ⟨c0, h⟩
  · obtain ⟨c0, h⟩ := hμ b c
    exact ⟨c0, h⟩

end CharacterConductor

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem step_ccBasic : CompactConductorBasicProp (k := k) :=
  CharacterConductor.step_ccBasic_of_cond

end Grp

end UpperTheory.TNZ
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.CharacterConductor =====

-- ===== clump member: PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.CharacterConductorBound =====
-- clump-header: {"m": "PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.CharacterConductorBound", "h": "module\n\npublic import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroLeviEigenvectorExists\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace Grp

namespace CharacterConductorBound

def Lv (ψ : 𝒪[k]ˣ →* ℂˣ) : Set ℕ :=
  {c | ∀ u : 𝒪[k]ˣ, (u : 𝒪[k]) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ c → ψ u = 1}

theorem exists_level (μ : kˣ →* ℂˣ) (hμ : IsSmoothChar μ) : (Lv (res μ)).Nonempty := by
  have hopen : IsOpen (μ.ker : Set kˣ) := hμ
  obtain ⟨V, hVo, hV⟩ := (Units.isEmbedding_val₀ (G₀ := k)).isInducing.isOpen_iff.mp hopen
  have h1 : (1 : k) ∈ V := by
    have : (1 : kˣ) ∈ (Units.val ⁻¹' V) := by rw [hV]; exact μ.ker.one_mem
    simpa using this
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_iff' (R := k)).mp (hVo.mem_nhds h1)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  have hlt : valuation k (algebraMap 𝒪[k] k ϖ) < 1 :=
    (Valuation.integer.integers (valuation k)).valuation_irreducible_lt_one hϖ
  have : MulArchimedean (ValueGroupWithZero k) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨c, hc⟩ := exists_pow_lt₀ hlt γ
  refine ⟨c, fun u hu => ?_⟩
  have hm : IsLocalRing.maximalIdeal 𝒪[k] = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hu
  obtain ⟨t, ht⟩ := hu
  have e : ((u : 𝒪[k]) : k) - 1 = (algebraMap 𝒪[k] k ϖ) ^ c * algebraMap 𝒪[k] k t := by
    have := congrArg (algebraMap 𝒪[k] k) ht
    simp only [map_sub, map_mul, map_pow, map_one] at this
    exact this
  have ht1 : valuation k (algebraMap 𝒪[k] k t) ≤ 1 := t.2
  have hv : valuation k (((u : 𝒪[k]) : k) - 1) < γ := by
    rw [e, map_mul, map_pow]
    calc valuation k (algebraMap 𝒪[k] k ϖ) ^ c * valuation k (algebraMap 𝒪[k] k t)
        ≤ valuation k (algebraMap 𝒪[k] k ϖ) ^ c * 1 := by gcongr
      _ < γ := by rw [mul_one]; exact hc
  have hmem : unitIncl k u ∈ (Units.val ⁻¹' V : Set kˣ) := hγ hv
  rw [hV] at hmem
  exact (MonoidHom.mem_ker).mp hmem

theorem max_mem (μ ν : kˣ →* ℂˣ) {c c' : ℕ} (hc : c ∈ Lv (res μ)) (hc' : c' ∈ Lv (res ν)) :
    max c c' ∈ Lv (res (μ / ν)) := by
  intro u hu
  have h1 := hc u (Ideal.pow_le_pow_right (le_max_left c c') hu)
  have h2 := hc' u (Ideal.pow_le_pow_right (le_max_right c c') hu)
  simp only [MonoidHom.comp_apply, MonoidHom.div_apply] at h1 h2 ⊢
  rw [h1, h2, div_one]

theorem cond_mem (ψ : 𝒪[k]ˣ →* ℂˣ) (h : (Lv ψ).Nonempty) : cond ψ ∈ Lv ψ := Nat.sInf_mem h

variable {n : ℕ} (G : Grp k n)

theorem lv_a (a : Fin G.s) : cond (res (G.μ a)) ∈ Lv (res (G.μ a)) :=
  cond_mem _ (exists_level _ (G.smooth a))

theorem lv_ab (a b : Fin G.s) :
    max (cond (res (G.μ a))) (cond (res (G.μ b))) ∈ Lv (res (G.μ a / G.μ b)) :=
  max_mem _ _ (lv_a G a) (lv_a G b)

theorem cc_le (a b : Fin G.s) : cc G.μ a b ≤ max (cond (res (G.μ a))) (cond (res (G.μ b))) :=
  Nat.sInf_le (lv_ab G a b)

theorem cc_mem (a b : Fin G.s) : cc G.μ a b ∈ Lv (res (G.μ a / G.μ b)) :=
  Nat.sInf_mem ⟨_, lv_ab G a b⟩

theorem cond_le_sum (a : Fin G.s) : cond (res (G.μ a)) ≤ ∑ b, cond (res (G.μ b)) :=
  Finset.single_le_sum (f := fun b => cond (res (G.μ b))) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)

theorem one_le_cc (a b : Fin G.s) (hab : a ≠ b) : 1 ≤ cc G.μ a b := by
  by_contra h0
  have h0' : cc G.μ a b = 0 := by omega
  have hm := cc_mem G a b
  rw [h0'] at hm
  apply G.dist a b hab
  ext u
  have := hm u (by simp)
  simp only [MonoidHom.comp_apply, MonoidHom.div_apply, div_eq_one] at this
  simp only [MonoidHom.comp_apply, this]

end CharacterConductorBound

theorem step_ccBound {n : ℕ} (G : Grp k n) : CompactConductorBoundProp G := by
  have hlev : G.lev = 1 + ∑ b, cond (res (G.μ b)) := rfl
  refine ⟨fun a b hab => CharacterConductorBound.one_le_cc G a b hab, fun a b => ?_, fun a => ?_,
    fun a b u hu => CharacterConductorBound.cc_mem G a b u hu⟩
  · have h1 := CharacterConductorBound.cc_le G a b
    have h2 := CharacterConductorBound.cond_le_sum G a
    have h3 := CharacterConductorBound.cond_le_sum G b
    rw [hlev]
    omega
  · have h2 := CharacterConductorBound.cond_le_sum G a
    rw [hlev]
    omega

end Grp

end UpperTheory.TNZ
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.CharacterConductorBound =====
