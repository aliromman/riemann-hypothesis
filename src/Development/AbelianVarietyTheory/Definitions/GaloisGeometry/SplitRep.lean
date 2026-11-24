module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
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

namespace GlobalTheory.SplitCoef

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual

def SplitRep {k Γ : Type} [Field k] [Group Γ] {a : ℕ} (ρ : Γ →* GL (Fin a) k) : Prop :=
  ∀ W, IsIrrSub ρ W → AbsIrrSub ρ W

def OSplitAt (D : D7) (i : D.nd.Loc) : Prop :=
  ∀ (x : D.nd.X i) (r : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)), IsHeckeGalois D.nd i x r →
    SplitRep (mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) r)

def OSplit (D : D7) : Prop := ∀ i, OSplitAt D i

end GlobalTheory.SplitCoef

end
