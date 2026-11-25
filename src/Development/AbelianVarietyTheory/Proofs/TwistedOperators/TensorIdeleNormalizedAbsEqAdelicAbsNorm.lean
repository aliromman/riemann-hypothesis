module

public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply

@[expose] public section

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

namespace GlobalTheory

theorem absE_eq_prod_norm_fstA_sndA (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E]
    [NumberField E] [Algebra F E] (y : (AF F ⊗[F] E)ˣ) :
    (∏ w, ‖(fstA F (Algebra.norm (AF F) (y : AF F ⊗[F] E))) w‖) *
      ∏ᶠ v, ‖evalV F v (sndA F (Algebra.norm (AF F) (y : AF F ⊗[F] E)))‖ = (GlobalTheory.Doubling.absE F E y : ℝ) := by
  have hf := GlobalTheory.Doubling.finite_mulSupport_absEv (F := F) (E := E) y
  rw [GlobalTheory.Doubling.absE_apply, NNReal.coe_mul, NNReal.coe_prod]
  simp only [GlobalTheory.Doubling.absEw_unitInf] at *
  simp only [GlobalTheory.Doubling.absEv_unitFin] at hf ⊢
  rw [show ((∏ᶠ v, ‖GlobalTheory.AdelicU.evFin F v (Algebra.norm (AF F) y.1)‖₊ : ℝ≥0) : ℝ) =
      ∏ᶠ v, ((‖GlobalTheory.AdelicU.evFin F v (Algebra.norm (AF F) y.1)‖₊ : ℝ≥0) : ℝ) from
    NNReal.toRealHom.toMonoidHom.map_finprod hf]
  congr 1
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [InfinitePlace.mult, if_pos (IsTotallyReal.isReal w), pow_one, coe_nnnorm]
  rfl

end GlobalTheory
