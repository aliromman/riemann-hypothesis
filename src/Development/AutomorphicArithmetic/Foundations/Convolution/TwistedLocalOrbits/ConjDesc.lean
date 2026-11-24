module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.InvTransposeGLInvTransposeGL
public import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.ConjSep
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IwahoriDoubleCosets
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace

@[expose] public section

open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc

theorem UpperTheory.ConvolutionTheory.Loc.conjDesc :
    ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (n : ℕ) (γ γ' : GL (Fin n) k), IsRegSemisimple γ →
      (∃ h : GL (Fin n) E, incl γ' = h * incl γ * h⁻¹) → ∃ y : GL (Fin n) k, γ' = y * γ * y⁻¹ := by
  intro k E _ _ _ n γ γ' hγ ⟨h, hh⟩
  have hc : (γ' : Matrix (Fin n) (Fin n) k).charpoly = (γ : Matrix (Fin n) (Fin n) k).charpoly := by
    apply Polynomial.map_injective (algebraMap k E) (algebraMap k E).injective
    rw [← Matrix.charpoly_map, ← Matrix.charpoly_map]
    have e := congrArg (fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E).charpoly) hh
    simp only [Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj] at e
    exact e
  obtain ⟨x, hx⟩ := (UpperTheory.ConvolutionTheory.D.conjSep k k n _ hγ).1 _ hc
  refine ⟨x⁻¹, ?_⟩
  have : γ * x = x * γ' := Units.ext hx
  rw [inv_inv, mul_assoc, this, inv_mul_cancel_left]
