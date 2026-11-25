module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.RhoFrob
public import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocA
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

open UpperTheory.V.Z.Kato.Joint

theorem UpperTheory.V.Z.Kato.Joint.jEx :
    UpperTheory.V.Z.Kato.Joint.JEx := by
  intro l _ Ω _ _ _ A hA
  obtain ⟨v, hv, hl⟩ := hA
  have hAl : A.valuation ((l : ℕ) : Ω) < 1 := by
    have := (hv ((l : ℕ) : NumberField.RingOfIntegers ℚ)).2 hl
    simpa using this
  exact ⟨(ValuationSubring.mem_nonunits_iff _).2 hAl, Formalism.BasicNotions.Examples₂.LB.exists_emb A hAl⟩
