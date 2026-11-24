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

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SplitColumnClasses

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG

def SplitsCompletely (E : Type) [Field E] [NumberField E] (p : ℕ) : Prop :=
  p.Prime ∧ (Formalism.BasicNotions.placesOver E p).ncard = Module.finrank ℚ E

theorem splitsCompletely_g (D : D7) (i : Fin 2) : SplitsCompletely D.host.E (D.host.g i) :=
  ⟨D.host.g_prime i, D.nd.g_split i⟩

end GlobalTheory.IndefiniteRowSideFullHecke.SplitColumnClasses

end
