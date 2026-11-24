module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.MixSeedPAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.OrdPlain
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

theorem UpperTheory.V.Z.Win.Birth.prOrd :
    UpperTheory.V.Z.Win.Birth.PrOrd := by
  intro F Ω _ _ _ _ _ _ l _ ι ξ s c m a π r h
  refine ⟨π, h.reg, h.att, fun v => ?_⟩
  by_cases hB : ∃ B, π.HasSat v B
  · exact Or.inr hB
  · exact Or.inl fun σ hσ =>
      (UpperTheory.V.Z.Win.Birth.ordPlain F Ω l ι ξ s c m a π r h v σ hσ).resolve_right hB
