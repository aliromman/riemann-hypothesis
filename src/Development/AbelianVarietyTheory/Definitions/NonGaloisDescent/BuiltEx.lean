module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
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

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain

namespace GlobalTheory.CoefDuty

variable {D : D7} {cf : CharFrame D} {jE : D.host.E →+* Qb}

def Built (A : SideA D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E)
    (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)) : Prop :=
  ∃ Sp : NdSpec A.pl M C big L.X L.T, Nonempty (AutSpec A M tup Sp.iq L.Y L.C) ∧ ∀ σ lam, IsSSRep (L.Z.rbar σ lam)

def ExtOf (L₀ L₁ : LocAll (lay0 D)) (i₀ : L₀.lay.fixZ.nd.Loc) (i₁ : L₁.lay.fixZ.nd.Loc) : Prop :=
  L₀.lay.fixZ.nd.w i₀ = L₁.lay.fixZ.nd.w i₁ ∧
    Nonempty (LocExt L₀.lay.fixZ.nd L₁.lay.fixZ.nd L₀.lay.fixZ.naut L₁.lay.fixZ.naut i₀ i₁)

end GlobalTheory.CoefDuty

end
