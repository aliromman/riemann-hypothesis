module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
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



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain
namespace GlobalTheory.CoefDuty
variable {D : D7} {cf : CharFrame D} {jE : D.host.E →+* Qb}
def BuiltAlt (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E)
    (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)) : Prop :=
  ∃ Sp : NdSpec A.pl M C big L.X L.T, Nonempty (_root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tup Sp.iq L.Y L.C) ∧ ∀ σ lam, IsSSRep (L.Z.rbar σ lam)
def AutomorphicSideExists (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) : Prop :=
  ∀ big, ∃ L, _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big L
def ForcedByAutomorphicSemisimpleData (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E)
    (P : D7 → Prop) : Prop :=
  ∃ big, ∀ L, _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big L → P (withLoc L)
end GlobalTheory.CoefDuty
end
end
