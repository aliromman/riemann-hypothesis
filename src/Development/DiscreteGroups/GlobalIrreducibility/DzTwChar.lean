module

public import Development.DiscreteGroups.GlobalIrreducibility.DzIsoRes
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

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace DiscreteGroups.sglob.DzTw

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)

include hi

def resMap : IsLocalRing.ResidueField 𝒪[w.adicCompletion E] →+* ZMod g :=
  Ideal.Quotient.lift (IsLocalRing.maximalIdeal 𝒪[w.adicCompletion E]) (DzIso.redO i hi) fun a ha => by
    rw [← RingHom.mem_ker, DzIso.ker_redO i hi]
    exact ha

end DiscreteGroups.sglob.DzTw
