module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.EntZero
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
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

noncomputable section

open NumberField

namespace PositivityTheory.Rg.BcB.F.gamma_zeta_nabla_cancel

open PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.SpectralAccumulation

def GelfInj : Prop :=
  ∀ (n : ℕ) (x y : Fin n → ℂ), (∀ m, GlobalTheory.Dec.gelfVal x m = GlobalTheory.Dec.gelfVal y m) →
    Finset.univ.val.map x = Finset.univ.val.map y

def RegDom : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (l : InfinitePlace E → Formalism.BasicNotions.DomWeight n),
    RealSym (mOf (fun v => PositivityTheory.RgBcC.infOf (l v).w)) ∧ ∀ τ, GapM (mOf (fun v => PositivityTheory.RgBcC.infOf (l v).w) τ)

def Reg : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (l : InfinitePlace E → Formalism.BasicNotions.DomWeight n)
    (χ : InfinitePlace E → PositivityTheory.RgBcC.Inf n),
    (∀ v s m, GlobalTheory.Dec.gelfVal (χ v s) m = GlobalTheory.Dec.gelfVal (PositivityTheory.RgBcC.infOf (l v).w s) m) →
      RealSym (mOf χ) ∧ ∀ τ, GapM (mOf χ τ)

end PositivityTheory.Rg.BcB.F.gamma_zeta_nabla_cancel

end
