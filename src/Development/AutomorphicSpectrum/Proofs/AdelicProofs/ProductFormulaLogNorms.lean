module

public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.RatProductFormula
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.SumLogEmbeddingsEqNorm
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem product_formula_embeddings (k : Type) [Field k] [NumberField k] (x : k) (hx : x ≠ 0) :
    {p | (LogNorms.ofElt x).finSum p ≠ 0}.Finite ∧
      (∑ s : k →+* ℂ, Real.log ‖s x‖) + ∑ᶠ p, (LogNorms.ofElt x).finSum p = 0 := by
  have hN : Algebra.norm ℚ x ≠ 0 := Algebra.norm_ne_zero_iff.mpr hx
  have hfin : ∀ p : Nat.Primes, (LogNorms.ofElt x).finSum p =
      Real.log ‖((Algebra.norm ℚ x : ℚ) : ℂ_[p])‖ := fun p =>
    sum_log_norm_embeddings_eq_log_norm k ℂ_[p] x hx
  have hinf := sum_log_norm_embeddings_eq_log_norm k ℂ x hx
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fl.rat_product_formula_complex (Algebra.norm ℚ x) hN
  simp only [hfin]
  exact ⟨h1, by rw [hinf]; exact h2⟩

end GlobalTheory.CompanionTheory.Ar.Fl
