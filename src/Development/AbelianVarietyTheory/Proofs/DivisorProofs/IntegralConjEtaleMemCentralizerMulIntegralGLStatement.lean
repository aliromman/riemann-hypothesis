module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralConjEtaleMemCentralizerMulIntegralGL
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

theorem _root_.GlobalTheory.T.integral_conj_etale_mem_centralizer_mul_integralGL : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E))
    (N g : GL (Fin n) (w.adicCompletion E)), N ∈ GlobalTheory.LFun.KGL w (n := n) →
    (∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧
      (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧ u * N.val.charpoly + v * derivative N.val.charpoly = 1) →
    g⁻¹ * N * g ∈ GlobalTheory.LFun.KGL w (n := n) → ∃ t : GL (Fin n) (w.adicCompletion E), t * N = N * t ∧ ∃ k ∈ GlobalTheory.LFun.KGL w (n := n), g = t * k := by
  first | exact @GlobalTheory.SplitUniq.splitUniq
