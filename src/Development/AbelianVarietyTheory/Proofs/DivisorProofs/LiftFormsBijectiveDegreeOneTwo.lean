module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleFormsCochainsEqDeRhamCochainsSmoothLif
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

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

theorem lift_forms_bij : ∀ (D : Data) (Λ : Lift D) (U : AffOp D.X),
    Function.Bijective (fun ω : Ω[Sec D.s U.unop.1⁄D.R] ↦
      (Submodule.Quotient.mk ((Λ.semi U).m1 ω) : K1 D.R (Λ.L.obj U).δ)) ∧
    Function.Bijective (fun x : Om D.R (Sec D.s U.unop.1) 2 ↦
      (Submodule.Quotient.mk ((Λ.semi U).mOm 2 x) : K D.R (Λ.L.obj U).δ 2)) :=
  fun _ Λ U ↦ ⟨LiftRes.liftOneFormsToCompatible_bijective Λ U, LiftRes.fm_bij Λ U 2⟩

end GlobalTheory.PDForm
