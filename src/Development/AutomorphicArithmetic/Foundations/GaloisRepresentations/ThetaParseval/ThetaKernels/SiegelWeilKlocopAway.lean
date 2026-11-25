module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
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



section
noncomputable section
open scoped Matrix Classical
open NumberField MeasureTheory GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def SD_k.IsAwayW (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) (Ψ : Mx F E d.m d.n → ℂ) : Prop :=
  ∀ X Z, (∀ w', w' ≠ w → d.cw w' Z = 0) → finOne F • Z = 0 → Ψ (X + Z) = Ψ X
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d)
def _root_.PositivityTheory.SiegelWeilFormula.RD_k.GoodAway (w : InfinitePlace F) (Ψ : Mx F E d.m d.n → ℂ) : Prop :=
  d.IsAwayW w Ψ ∧ Ψ ≠ 0 ∧ ∀ f, IsSw f → R.tens w f Ψ ∈ d.schM
end RD
def GoodAwayEx_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
  (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F), ∃ Ψ, R.GoodAway w Ψ
end PositivityTheory.SiegelWeilFormula
end
end
