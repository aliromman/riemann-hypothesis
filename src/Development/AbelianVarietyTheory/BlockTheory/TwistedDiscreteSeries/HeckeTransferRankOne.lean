module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
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
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.IndefiniteRowSideFullHecke.HeckeTransferRankOne

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
  Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Real

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

end Real

theorem rank_Vc (i : Fin D.R.m) : (Vc D i).rank = D.R.nV ∧ D.R.nV = D.R.r + D.R.t :=
  ⟨D.sp.V_rank _ (Nat.le_add_left _ _) i.2, rfl⟩

end GlobalTheory.IndefiniteRowSideFullHecke.HeckeTransferRankOne
