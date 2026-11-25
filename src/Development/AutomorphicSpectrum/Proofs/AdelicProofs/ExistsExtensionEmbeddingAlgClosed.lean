module

public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes

@[expose] public section

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem exists_comp_eq_of_numberField (k k' A : Type) [Field k] [NumberField k] [Field k']
    [NumberField k'] [Field A] [CharZero A] [IsAlgClosed A] (f : k →+* k') (j : k →+* A) :
    ∃ j' : k' →+* A, j'.comp f = j := by
  let _ : Algebra k k' := f.toAlgebra
  let _ : Algebra k A := j.toAlgebra
  have : IsScalarTower ℚ k k' := IsScalarTower.of_algebraMap_eq fun q => by
    rw [RingHom.algebraMap_toAlgebra, eq_ratCast (algebraMap ℚ k') q, eq_ratCast (algebraMap ℚ k) q,
      map_ratCast]
  have : Module.Finite k k' := Module.Finite.of_restrictScalars_finite ℚ k k'
  have : Algebra.IsAlgebraic k k' := Algebra.IsAlgebraic.of_finite k k'
  refine ⟨(IsAlgClosed.lift : k' →ₐ[k] A).toRingHom, ?_⟩
  ext x
  exact (IsAlgClosed.lift : k' →ₐ[k] A).commutes x

end GlobalTheory.CompanionTheory.Ar.Fl
