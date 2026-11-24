module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FSatakeB
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFourLeviGL2CartanDoubleCosets, Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFourLeviGL2RootIndexOfCardSq

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFourLeviGL2CartanDoubleCosets =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFourLeviGL2CartanDoubleCosets", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply\nimport Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FSatakeB\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl.Four

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}

def unitaryFourUpperLeftBlock (g : GU σ 4) : Matrix (Fin 2) (Fin 2) L := !![mat g 0 0, mat g 0 1; mat g 1 0, mat g 1 1]

theorem unitaryFourUpperLeftBlock_mul_of_mem_levi {g : GU σ 4} (g' : GU σ 4) (hg : g ∈ leviU σ ![0, 0, 1, 1]) :
    unitaryFourUpperLeftBlock (g * g') = unitaryFourUpperLeftBlock g * unitaryFourUpperLeftBlock g' := by
  have h02 := hg 0 2 (by decide)
  have h03 := hg 0 3 (by decide)
  have h12 := hg 1 2 (by decide)
  have h13 := hg 1 3 (by decide)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unitaryFourUpperLeftBlock, mat_mul, Matrix.mul_apply, Fin.sum_univ_four, h02, h03, h12, h13]

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem unitaryFourUpperLeftBlock_one : unitaryFourUpperLeftBlock (1 : GU σ 4) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unitaryFourUpperLeftBlock, mat_one]

theorem unitaryFourUpperLeftBlock_injective_on_levi {g g' : GU σ 4} (hg : g ∈ leviU σ ![0, 0, 1, 1]) (hg' : g' ∈ leviU σ ![0, 0, 1, 1])
    (h : unitaryFourUpperLeftBlock g = unitaryFourUpperLeftBlock g') : g = g' := by
  have h1 : unitaryFourUpperLeftBlock g⁻¹ * unitaryFourUpperLeftBlock g' = 1 := by
    rw [← h, ← unitaryFourUpperLeftBlock_mul_of_mem_levi _ (inv_mem hg), inv_mul_cancel, unitaryFourUpperLeftBlock_one]
  have h2 : unitaryFourUpperLeftBlock g' * unitaryFourUpperLeftBlock g'⁻¹ = 1 := by
    rw [← unitaryFourUpperLeftBlock_mul_of_mem_levi _ hg', mul_inv_cancel, unitaryFourUpperLeftBlock_one]
  have h3 : unitaryFourUpperLeftBlock g⁻¹ = unitaryFourUpperLeftBlock g'⁻¹ := left_inv_eq_right_inv h1 h2
  have low : ∀ i j : Fin 4, mat g⁻¹ j.rev i.rev = mat g'⁻¹ j.rev i.rev → mat g i j = mat g' i j := by
    intro i j e
    have e1 := mat_inv_apply g⁻¹ i j
    have e2 := mat_inv_apply g'⁻¹ i j
    rw [inv_inv] at e1 e2
    rw [e1, e2, e]
  have off : ∀ i j : Fin 4, (![0, 0, 1, 1] : Fin 4 → ℕ) i ≠ ![0, 0, 1, 1] j → mat g i j = mat g' i j :=
    fun i j e => by rw [hg i j e, hg' i j e]
  apply mat_injective
  ext i j
  fin_cases i <;> fin_cases j
  · exact congrFun (congrFun h 0) 0
  · exact congrFun (congrFun h 0) 1
  · exact off _ _ (by decide)
  · exact off _ _ (by decide)
  · exact congrFun (congrFun h 1) 0
  · exact congrFun (congrFun h 1) 1
  · exact off _ _ (by decide)
  · exact off _ _ (by decide)
  · exact off _ _ (by decide)
  · exact off _ _ (by decide)
  · exact low _ _ (congrFun (congrFun h3 1) 1)
  · exact low _ _ (congrFun (congrFun h3 0) 1)
  · exact off _ _ (by decide)
  · exact off _ _ (by decide)
  · exact low _ _ (congrFun (congrFun h3 1) 0)
  · exact low _ _ (congrFun (congrFun h3 0) 0)

theorem exists_lift (h1 : ∀ x, σ (σ x) = x) (h2 : ∀ x, Valued.v (σ x) = Valued.v x) {p r u w : L}
    (hp : p ∈ intL L) (hr : r ∈ intL L) (hu : u ∈ intL L) (hw : w ∈ intL L) (hd : p * w - r * u = -1) :
    ∃ k ∈ KU σ 4 ⊓ leviU σ ![0, 0, 1, 1], unitaryFourUpperLeftBlock k = !![p, r; u, w] := by
  have hd' : σ p * σ w - σ r * σ u = -1 := by simpa using congrArg σ hd
  have hs : ∀ x ∈ intL L, σ x ∈ intL L := fun x hx => by
    show Valued.v (σ x) ≤ 1
    rw [h2]; exact hx
  obtain ⟨k, hk⟩ := exists_mat (σ := σ) !![p, r, 0, 0; u, w, 0, 0; 0, 0, -σ p, σ r; 0, 0, σ u, -σ w] (by
    ext i j
    rw [Matrix.mul_apply]
    simp only [P.fSatake_cTJ]
    fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_four, antiJ, h1, Fin.rev] <;>
      first | linear_combination hd | linear_combination -hd | linear_combination hd' | linear_combination -hd' | ring)
  refine ⟨k, ⟨(mem_KU_iff h2 k).2 fun i j => ?_, fun i j hij => ?_⟩, ?_⟩
  · rw [hk]
    fin_cases i <;> fin_cases j <;> simp [hp, hr, hu, hw, hs _ hp, hs _ hr, hs _ hu, hs _ hw]
  · rw [hk]
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · simp [unitaryFourUpperLeftBlock, hk]

theorem exists_conj {A D ξ : L} (hA : A ≠ 0) (hD : D ≠ 0) :
    ∃ p ∈ intL L, ∃ r ∈ intL L, ∃ u ∈ intL L, ∃ w ∈ intL L, p * w - r * u = -1 ∧
      !![D, -(A * ξ); 0, A] = !![p, r; u, w] * !![A, A * ξ; 0, D] * !![p, r; u, w] := by
  have mem : ∀ x : L, x ∈ intL L ↔ Valued.v x ≤ 1 := fun x => Iff.rfl
  by_cases h1 : ξ ∈ intL L
  · refine ⟨-ξ, neg_mem h1, 1, one_mem _, 1, one_mem _, 0, zero_mem _, by ring, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  by_cases h2 : A * ξ / D ∈ intL L
  · refine ⟨0, zero_mem _, 1, one_mem _, 1, one_mem _, -(A * ξ / D), neg_mem h2, by ring, ?_⟩
    obtain ⟨ζ, hζ⟩ : ∃ ζ, A * ξ = D * ζ := ⟨A * ξ / D, by field_simp⟩
    rw [hζ, mul_div_cancel_left₀ _ hD]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
  have hξ : ξ ≠ 0 := fun e => h1 (e ▸ zero_mem _)
  have inv : ∀ x : L, x ∉ intL L → x⁻¹ ∈ intL L := fun x hx => by
    rw [mem] at hx ⊢
    rw [map_inv₀]
    exact inv_le_one_of_one_le₀ (not_le.1 hx).le
  refine ⟨1, one_mem _, 0, zero_mem _, -(ξ⁻¹ - (A * ξ / D)⁻¹), neg_mem (sub_mem (inv _ h1) (inv _ h2)),
    -1, neg_mem (one_mem _), by ring, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

theorem cartanFour : GlobalTheory.SatakeWeyl.CartanFour := by
  intro L _ _ ϖ σ q hU x y s s' hs hs' a ha
  obtain ⟨h1, h2, -, h4, -⟩ := hU
  have hϖ : ϖ ≠ 0 := fun e => by rw [e, map_zero] at h4; exact WithZero.zero_ne_coe h4
  have dl : ∀ (t : GU σ 4) (d : Fin 4 → L), mat t = Matrix.diagonal d → t ∈ leviU σ ![0, 0, 1, 1] :=
    fun t d e i j hij => by rw [e]; exact Matrix.diagonal_apply_ne _ fun e => hij (e ▸ rfl)
  have hsl := dl _ _ hs
  have hsl' := dl _ _ hs'
  have us : unitaryFourUpperLeftBlock s = !![ϖ ^ x, 0; 0, ϖ ^ y] := by simp [unitaryFourUpperLeftBlock, hs]
  have us' : unitaryFourUpperLeftBlock s' = !![ϖ ^ y, 0; 0, ϖ ^ x] := by simp [unitaryFourUpperLeftBlock, hs']
  have ua : unitaryFourUpperLeftBlock a = !![1, mat a 0 1; 0, 1] := by
    simp [unitaryFourUpperLeftBlock, ha.1 0 0 (by decide), ha.1 1 0 (by decide), ha.1 1 1 (by decide)]
  obtain ⟨p, hp, r, hr, u, hu, w, hw, hd, e⟩ :=
    exists_conj (ξ := mat a 0 1) (zpow_ne_zero x hϖ) (zpow_ne_zero y hϖ)
  obtain ⟨k, hk, uk⟩ := exists_lift h1 h2 hp hr hu hw hd
  refine ⟨k, hk.1, k, hk, ?_⟩
  rw [inv_mul_eq_iff_eq_mul]
  refine unitaryFourUpperLeftBlock_injective_on_levi hsl' (mul_mem ha.2 (mul_mem (mul_mem hk.2 (mul_mem hsl ha.2)) hk.2)) ?_
  have usa : unitaryFourUpperLeftBlock (s * a) = !![ϖ ^ x, ϖ ^ x * mat a 0 1; 0, ϖ ^ y] := by
    rw [unitaryFourUpperLeftBlock_mul_of_mem_levi _ hsl, us, ua]; simp
  rw [unitaryFourUpperLeftBlock_mul_of_mem_levi _ ha.2, unitaryFourUpperLeftBlock_mul_of_mem_levi _ (mul_mem hk.2 (mul_mem hsl ha.2)), unitaryFourUpperLeftBlock_mul_of_mem_levi _ hk.2, usa, uk, ← e, us', ua]
  simp [mul_comm]

end GlobalTheory.SatakeWeyl.Four

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFourLeviGL2CartanDoubleCosets =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFourLeviGL2RootIndexOfCardSq =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFourLeviGL2RootIndexOfCardSq", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply\nimport Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FSatakeB\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Formalism.UG

namespace GlobalTheory.SatakeWeyl.IdxFour

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}

def rootMat (σ : L →+* L) (x : L) : Matrix (Fin 4) (Fin 4) L :=
  !![1, x, 0, 0; 0, 1, 0, 0; 0, 0, 1, -σ x; 0, 0, 0, 1]

theorem rootMat_unitary (hσ : ∀ x, σ (σ x) = x) (x : L) :
    cT σ (rootMat σ x) * antiJ L 4 * rootMat σ x = antiJ L 4 := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [P.fSatake_cTJ, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;> simp [rootMat, antiJ, Fin.rev, hσ]

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem rootMat_add (x y : L) : rootMat σ (x + y) = rootMat σ x * rootMat σ y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rootMat, Matrix.mul_apply, Fin.sum_univ_four, add_comm]

theorem exists_hom (hσ : ∀ x, σ (σ x) = x) :
    ∃ φ : Multiplicative L →* GU σ 4, ∀ x, mat (φ x) = rootMat σ x.toAdd := by
  choose f hf using fun x : L => exists_mat (rootMat σ x) (rootMat_unitary hσ x)
  refine ⟨MonoidHom.mk' (fun x => f x.toAdd) fun a b => mat_injective ?_, fun x => hf _⟩
  rw [mat_mul, hf, hf, hf, toAdd_mul, rootMat_add]

theorem mat_of_mem (hσ : ∀ x, σ (σ x) = x) {g : GU σ 4} (hg : g ∈ rootU σ ![0, 0, 1, 1]) :
    mat g = rootMat σ (mat g 0 1) := by
  have h1 : ∀ i j : Fin 4, j.val ≤ i.val → mat g i j = (1 : Matrix (Fin 4) (Fin 4) L) i j := hg.1
  have h2 : ∀ i j : Fin 4, (![0, 0, 1, 1] : Fin 4 → ℕ) i ≠ (![0, 0, 1, 1] : Fin 4 → ℕ) j → mat g i j = 0 := hg.2
  have h3 : cT σ (mat g) * antiJ L 4 * mat g = antiJ L 4 := g.2
  have h4 := congrFun (congrFun h3 1) 3
  rw [Matrix.mul_apply] at h4
  simp only [P.fSatake_cTJ, Fin.sum_univ_four] at h4
  have e00 := h1 0 0 (by decide)
  have e11 := h1 1 1 (by decide)
  have e22 := h1 2 2 (by decide)
  have e33 := h1 3 3 (by decide)
  have e10 := h1 1 0 (by decide)
  have e32 := h1 3 2 (by decide)
  have e02 := h2 0 2 (by decide)
  have e03 := h2 0 3 (by decide)
  have e12 := h2 1 2 (by decide)
  have e13 := h2 1 3 (by decide)
  have e20 := h2 2 0 (by decide)
  have e21 := h2 2 1 (by decide)
  have e30 := h2 3 0 (by decide)
  have e31 := h2 3 1 (by decide)
  have r0 : Fin.rev (0 : Fin 4) = 3 := rfl
  have r1 : Fin.rev (1 : Fin 4) = 2 := rfl
  have r2 : Fin.rev (2 : Fin 4) = 1 := rfl
  have r3 : Fin.rev (3 : Fin 4) = 0 := rfl
  rw [r0, r1, r2, r3, e03, e13, e11, e33] at h4
  have e23 : mat g 2 3 = -σ (mat g 0 1) := by
    simp [antiJ] at h4
    exact eq_neg_of_add_eq_zero_left h4
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rootMat, *]

theorem mem_root {g : GU σ 4} {x : L} (hg : mat g = rootMat σ x) : g ∈ rootU σ ![0, 0, 1, 1] := by
  refine ⟨fun i j h => ?_, fun i j h => ?_⟩
  · rw [hg]
    fin_cases i <;> fin_cases j <;> simp [rootMat] at h ⊢
  · rw [hg]
    fin_cases i <;> fin_cases j <;> simp [rootMat] at h ⊢

theorem mem_K_iff (hv : ∀ x, Valued.v (σ x) = Valued.v x) {g : GU σ 4} {x : L} (hg : mat g = rootMat σ x) :
    g ∈ KU σ 4 ↔ x ∈ intL L := by
  rw [mem_KU_iff hv, hg]
  refine ⟨fun h => by simpa [rootMat] using h 0 1, fun h i j => ?_⟩
  have h' : σ x ∈ intL L := by
    show Valued.v (σ x) ≤ 1
    rw [hv]
    exact h
  fin_cases i <;> fin_cases j <;> simp [rootMat, h, h', one_mem, zero_mem]

theorem indexFour (hI : IntIndex) : IndexFour := by
  intro L _ _ ϖ σ q hU s₀ hs
  obtain ⟨φ, hφ⟩ := exists_hom hU.1
  have hϖ : ϖ ≠ 0 := by
    rintro rfl
    have := hU.2.2.2.1
    simp at this
  have hinj : Function.Injective φ := fun a b h => by
    have := congrFun (congrFun ((hφ a).symm.trans ((congrArg mat h).trans (hφ b))) 0) 1
    simpa [rootMat] using this
  have hK : KU σ 4 ⊓ rootU σ ![0, 0, 1, 1] = (AddSubgroup.toSubgroup (intL L).toAddSubgroup).map φ := by
    ext g
    constructor
    · rintro ⟨h1, h2⟩
      have e := mat_of_mem hU.1 h2
      exact ⟨Multiplicative.ofAdd (mat g 0 1), (mem_K_iff hU.2.1 e).1 h1, mat_injective ((hφ _).trans e.symm)⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(mem_K_iff hU.2.1 (hφ x)).2 hx, mem_root (hφ x)⟩
  have hc : ∀ x : L, s₀ * φ (Multiplicative.ofAdd x) * s₀⁻¹ = φ (Multiplicative.ofAdd (ϖ * x)) := by
    intro x
    rw [mul_inv_eq_iff_eq_mul]
    apply mat_injective
    rw [mat_mul, mat_mul, hφ, hφ, hs]
    ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    fin_cases i <;> fin_cases j <;> simp [rootMat, hU.2.2.1]
    field_simp
  have hK' : ((AddSubgroup.toSubgroup (intL L).toAddSubgroup).map φ).map (MulAut.conj s₀).toMonoidHom =
      (AddSubgroup.toSubgroup ((intL L).toAddSubgroup.map (AddMonoidHom.mulLeft ϖ))).map φ := by
    ext g
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨Multiplicative.ofAdd (ϖ * x.toAdd), ⟨x.toAdd, hx, rfl⟩, (hc x.toAdd).symm⟩
    · rintro ⟨y, ⟨x, hx, e⟩, rfl⟩
      refine ⟨φ (Multiplicative.ofAdd x), ⟨_, hx, rfl⟩, (hc x).trans (congrArg φ ?_)⟩
      exact congrArg Multiplicative.ofAdd e
  rw [hK, hK', Subgroup.relIndex_map_map_of_injective _ _ hinj, AddSubgroup.relIndex_toSubgroup]
  exact hI L ϖ σ q hU

end GlobalTheory.SatakeWeyl.IdxFour

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFourLeviGL2RootIndexOfCardSq =====
