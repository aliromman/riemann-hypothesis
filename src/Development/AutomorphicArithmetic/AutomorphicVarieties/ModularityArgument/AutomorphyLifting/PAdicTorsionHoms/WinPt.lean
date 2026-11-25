module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PlainAtR
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.PlainIff
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.WeakOfAtt

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.Zero.LLC UpperTheory.V UpperTheory.V.Af UpperTheory.V.Z.Gam UpperTheory.V.Z.Win
open GroundTheory.Global.SemiLocal UpperTheory.V.Published

theorem UpperTheory.V.Z.Win.winPt :
    Z.Gam.SuppFacts → ImaginaryQuadraticEtaCharacter.WinOf → WinPt := by
  intro _ hW K _ _ _ n hn π
  obtain ⟨t, ht⟩ := hW K n hn π
  refine ⟨t, fun v h => ?_⟩
  have e := (UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.plainIff K n hn π v).1 h
  exact ht v e.1 e.2
