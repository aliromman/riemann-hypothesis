module

public import Formalism.CyclotomicNorms.StatementT
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

noncomputable section

namespace GlobalTheory.TypeLeaf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.TameLabels

theorem map_primeToPart_fbar {g l : ℕ} [Fact g.Prime] [Fact l.Prime] {K : Type} [Field K] [CharP K l]
    (ι : Formalism.CyclotomicNorms.Fbar g →* K) (x : Formalism.CyclotomicNorms.Fbar g) : ι (Formalism.CyclotomicNorms.primeToPart l x) = ι x := by
  by_cases hx : x = 0
  · subst hx
    simp [Formalism.CyclotomicNorms.primeToPart, ZMod.val_one_eq_one_mod]
  · exact map_primeToPart ι (isOfFinOrder_of_ne_zero hx)

end GlobalTheory.TypeLeaf
