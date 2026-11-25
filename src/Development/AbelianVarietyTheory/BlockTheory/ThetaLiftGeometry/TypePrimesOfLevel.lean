module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
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
import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnipotentLevelStabilisers

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col

section Generic

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}


end Generic

variable (D : D7)


def TypePrimesLarge : Prop := ∀ i, 2 * D.R.f * D.R.k + 1 < D.host.g i

end GlobalTheory.IndefiniteRowSideFullHecke.UnipotentLevelStabilisers

end
