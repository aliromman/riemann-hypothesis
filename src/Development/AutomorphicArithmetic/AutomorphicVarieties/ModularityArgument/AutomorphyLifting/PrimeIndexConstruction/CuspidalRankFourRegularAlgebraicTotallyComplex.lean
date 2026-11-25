module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.WinUpDown
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.LocTrans
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.ResLeCont
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SphericalOfHasSat

@[expose] public section

open UpperTheory.GalN.V UpperTheory.V.Ws.Pt UpperTheory.V.Z.Win

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.CuspRep GlobalTheory.GalOfCusp Formalism.BasicNotions Formalism.MainNotions.N

namespace UpperTheory.V.Z.Win.Birth

def CuspidalRankFourRegularAlgebraicTotallyComplex {L : Type} [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] (π : CuspSub L 4) : Prop := (CG.mk π).IsRegAlg ∧ ImaginaryQuadraticEtaCharacter.AllWin π

theorem mkReg' {L : Type} [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] {π : CuspSub L 4} (h : (CG.mk π).IsRegAlg) (u : ImaginaryQuadraticEtaCharacter.AllWin π) :
    CuspidalRankFourRegularAlgebraicTotallyComplex π := ⟨h, u⟩

end UpperTheory.V.Z.Win.Birth
