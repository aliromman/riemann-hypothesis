module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
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

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LocAcyc

def genFibMap {T E O : Type} [CommRing T] [CommRing E] [CommRing O] [Algebra T E] [Algebra T O]
    (ψ : E →ₐ[T] O) : GenFib T E →+* GenFib T O :=
  IsLocalization.map (M := Algebra.algebraMapSubmonoid E (nonZeroDivisors T))
    (T := Algebra.algebraMapSubmonoid O (nonZeroDivisors T)) (GenFib T O) ψ.toRingHom (by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨t, ht, (ψ.commutes t).symm⟩)

theorem genFibMap_algebraMap {T E O : Type} [CommRing T] [CommRing E] [CommRing O] [Algebra T E]
    [Algebra T O] (ψ : E →ₐ[T] O) (e : E) :
    genFibMap ψ (algebraMap E (GenFib T E) e) = algebraMap O (GenFib T O) (ψ e) := by
  simp [genFibMap, IsLocalization.map_eq]

theorem genFib_ringHom_ext {T E C : Type} [CommRing T] [CommRing E] [CommRing C] [Algebra T E]
    {f g : GenFib T E →+* C} (h : ∀ e : E, f (algebraMap E _ e) = g (algebraMap E _ e)) : f = g :=
  IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid E (nonZeroDivisors T))
    (RingHom.ext h)

end GlobalTheory.LocAcyc
