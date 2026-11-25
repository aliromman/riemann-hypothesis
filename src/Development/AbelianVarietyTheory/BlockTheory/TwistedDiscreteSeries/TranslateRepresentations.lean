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

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev

namespace GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations

variable {D : D7}

section Space

variable (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)

def LiftsTo (κ : (levEnv V β L).Q) (g₀ : G0 L.Pg L.r) : Prop :=
  rTup β L (Formalism.UG.bc (swapAE D) ((κ : Bridge.Gf V) : GL _ _)) = g₀

def IsTranslate {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (g₀ : G0 L.Pg L.r) (F F' : Bridge.Gf V → W) : Prop :=
  (∃ κ, LiftsTo V β L κ g₀) ∧
    ∀ κ, LiftsTo V β L κ g₀ → ∀ h, F' h = ((((levEnv V β L).ch κ)⁻¹ : ℂˣ) : ℂ) • F (h * (κ : Bridge.Gf V))

variable {V β L}

end Space

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)


end GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations

end
