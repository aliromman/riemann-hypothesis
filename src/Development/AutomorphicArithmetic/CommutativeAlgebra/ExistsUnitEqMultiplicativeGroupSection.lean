module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlue
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleToSheafifyLocallyBijectiveAndLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqPowOfKummerClassOfUnitEqZero
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Tactic.Lemma
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

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace UpperTheory
open Polynomial

private def evalX {A : Type} [CommRing A] (a : A) : ℤ[X] →+* A := Polynomial.eval₂RingHom (Int.castRingHom A) a

private lemma evalX_X {A : Type} [CommRing A] (a : A) : evalX a X = a := by simp [evalX]

private abbrev TT : Scheme.{0} := Spec (CommRingCat.of ℤ[X])

end UpperTheory

open UpperTheory in
theorem UpperTheory.exists_unit_eq_multiplicativeGroup_section :
    ∀ (X : Scheme.{0}) (b : Sec Gm X), ∃ u : (Γ(X, ⊤))ˣ, unitSec u = b := by
  apply GlobalTheory.EtC.KumZero.unitSec_surjective

end
