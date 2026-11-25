module

public import Formalism.LocalToGlobal.Columns.StdLatUnimodular
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

namespace GlobalTheory.InertExchange

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.L2.Col

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}


open Classical in
def patchAt (P : HeightOneSpectrum (𝓞 E)) (A B : Submodule (𝓞 E) (Sp E n)) : Submodule (𝓞 E) (Sp E n) :=
  ⨅ Q : HeightOneSpectrum (𝓞 E), localization₂ Q.asIdeal (if Q = P then A else B)

end GlobalTheory.InertExchange
