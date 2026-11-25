module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.RhoKApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.IsAutCsdA
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section




section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg
open IsLocalRing Matrix Formalism.MainNotions.N GlobalTheory.GalOfCusp
namespace UpperTheory.V.U3
namespace Dat
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
  {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ)
def IsAutIAlt [IsCMField K] (ι : Qbar l ≃+* ℂ) (r : G ℚ Ω →* GG (m := 3) (R := PadicAlgCl l))
    (hr : HasMult D.η r) : Prop :=
  _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (Af.tw (D.rhoK r hr) (cycBar K Ω l)⁻¹)
end Dat
end UpperTheory.V.U3
end
end
