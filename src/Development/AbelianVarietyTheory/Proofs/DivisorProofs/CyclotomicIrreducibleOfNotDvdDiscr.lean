module

public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
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
public import ReciprocityTheory.Chebotarev.CyclotomicIrreducibleOfForallIsUnramifiedAt

@[expose] public section

namespace GlobalTheory

open Polynomial NumberField

theorem cyclotomic_irreducible_of_not_dvd_discr :
    ∀ (E : Type) [Field E] [NumberField E] (l : ℕ), l.Prime → ¬ (l : ℤ) ∣ NumberField.discr E →
      Irreducible (Polynomial.cyclotomic l E) := by
  intro E _ _ l hl hd
  refine ReciprocityTheory.Cheb.cyclotomic_irreducible_of_forall_isUnramifiedAt hl fun P hP hlP => ?_
  exact (not_dvd_discr_iff_forall_mem E (𝓞 E) (Nat.prime_iff_prime_int.1 hl)).1 hd P hP
    (by simpa using hlP)

end GlobalTheory
