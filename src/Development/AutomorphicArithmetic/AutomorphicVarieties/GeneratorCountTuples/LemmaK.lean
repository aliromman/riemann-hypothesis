module

public import Formalism.GaloisCohomology.Statement
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
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

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology

namespace UpperTheory.V

def HasMuQ (l : ℕ) (L : Type) [Field L] : Prop := ∃ ζ : L, IsPrimitiveRoot ζ (if l = 2 then 4 else l)

def kBound (C : ℝ) (e n D : ℕ) : ℝ := Real.exp ((2 * (e : ℝ) * n) ^ C * Real.log (2 * (D : ℝ)))

def LemmaK (CK : ℝ) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (D : LData L Ω l), IsTotallyComplex L → HasMuQ l L → ∀ e : ℕ, 1 ≤ e →
      Finite (H2 (zlTw D ((e : ℤ) + 1))) ∧
        Real.log (Nat.card (H2 (zlTw D ((e : ℤ) + 1)))) ≤ kBound CK e (Module.finrank ℚ L) (discr L).natAbs

end UpperTheory.V

end
