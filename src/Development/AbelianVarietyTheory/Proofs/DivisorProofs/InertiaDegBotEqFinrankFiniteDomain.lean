module

public import Mathlib.RingTheory.RamificationInertia.Inertia
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

@[expose] public section

namespace GlobalTheory

theorem inertiaDeg_bot_eq_finrank : ∀ (R S : Type) [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S], Function.Injective (algebraMap R S) → (⊥ : Ideal S).inertiaDeg R = Module.finrank R S := by
  intro R S _ _ _ _ _ _ hinj
  haveI : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).2 hinj
  haveI : (⊥ : Ideal S).LiesOver (⊥ : Ideal R) :=
    ⟨(Ideal.comap_bot_of_injective (algebraMap R S) hinj).symm⟩
  letI := Localization.AtPrime.algebraOfLiesOver (⊥ : Ideal R) (⊥ : Ideal S)
  rw [Ideal.inertiaDeg_eq (⊥ : Ideal R) (⊥ : Ideal S)]
  exact IsFractionRing.finrank_eq R (⊥ : Ideal R).ResidueField S
    (⊥ : Ideal S).ResidueField

end GlobalTheory
