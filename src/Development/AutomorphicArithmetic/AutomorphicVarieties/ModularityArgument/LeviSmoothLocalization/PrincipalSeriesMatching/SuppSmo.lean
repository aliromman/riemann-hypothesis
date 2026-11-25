module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.WinUpDown
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.Strong
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

open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.suppSmo :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.SuppSmo := by
  intro K _ _ _ n _ π π' h t v hw
  have e : π = π' := GlobalTheory.CuspRep.CuspSub.ext (UpperTheory.V.Af.strongMultOneC K n π π'
    (h.mono fun w ⟨B, h₁, h₂⟩ =>
      ⟨B, (GlobalTheory.CuspRep.CG.hasSat_mk π w B).1 h₁, (GlobalTheory.CuspRep.CG.hasSat_mk π' w B).1 h₂⟩))
  exact e ▸ hw
