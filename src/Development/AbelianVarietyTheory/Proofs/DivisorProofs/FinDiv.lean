module

public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
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

namespace GlobalTheory.FinSupp

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU

variable (F : Type) [Field F] [NumberField F]

def FinDiv (N : ℕ) (a : AF F) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 F), ∃ b ∈ v.adicCompletionIntegers F, evFin F v a = (N : Fv F v) * b

def finPart (a : AF F) : AF F := (0, a.2)

end GlobalTheory.FinSupp
