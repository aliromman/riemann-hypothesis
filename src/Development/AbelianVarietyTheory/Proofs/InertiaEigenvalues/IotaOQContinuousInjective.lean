module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowLeSpan
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
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders

@[expose] public section

namespace GlobalTheory.TypeLeaf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain


open Polynomial NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.TypeLeaf.iotaOQ_continuous_injective (D : _root_.Formalism.BasicNotions.D7) (i : D.nd.Loc) :
    Continuous (_root_.Formalism.MainNotions.N.iotaOQ D.nd D.naut i) ∧ Function.Injective (_root_.Formalism.MainNotions.N.iotaOQ D.nd D.naut i) := by
  refine ⟨_root_.GlobalTheory.CoeffEmbedding.continuous_iotaOQ _ _ _ D.nd D.naut i, ?_⟩
  unfold _root_.Formalism.MainNotions.N.iotaOQ
  exact (D.naut.iotaQ i).injective.comp (IsFractionRing.injective _ _)

end GlobalTheory.TypeLeaf
