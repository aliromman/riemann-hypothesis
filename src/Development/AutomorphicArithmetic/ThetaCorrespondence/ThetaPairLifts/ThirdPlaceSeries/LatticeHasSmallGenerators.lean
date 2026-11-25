module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvOfRoot
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
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
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct


namespace GlobalTheory.BigOn.Exp
def ReadInjAlt : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x _ i p w j => ∀ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (ν : ℂ), ν ≠ 0 →
  Function.Injective (rdAt p w j hρ ν)
def LatticeHasSmallGenerators : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ : Setup (Fm.D x i).ntw), ρ.Good → RealPin p.R p.cG ρ →
  ∀ (h : GA (Fm.D x i) (Vc (Fm.D x i) j)) (P : PolF (Fm.D x i) (Wc (Fm.D x i) j).rank (Vc (Fm.D x i) j).rank),
    P ∈ ρ.lat ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
      (ρ.eO ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w)).range h →
    P ∈ Submodule.span (ρ.eO ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w)).range
      (ρ.lat ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (smallInt (Fm.D x i)) h :
        Set (PolF (Fm.D x i) (Wc (Fm.D x i) j).rank (Vc (Fm.D x i) j).rank))
end GlobalTheory.BigOn.Exp
end
end
