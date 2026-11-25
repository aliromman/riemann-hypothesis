module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsUnitarisableTrivChar
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.Narrow
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.NarrowAsc
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.NarrowSpeh
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso

@[expose] public section




section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
namespace UpperTheory.BaseChangeIdentities
theorem bcSpeh_alt : DefiniteN → GlobalTheory.BcSpeh.BcSpeh :=
  fun h => bcSpeh_of ascComp h
end UpperTheory.BaseChangeIdentities
end
end
