module

public import Mathlib.RingTheory.Length
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
import Mathlib.Tactic.TypeStar

@[expose] public section

open NumberField IsDedekindDomain IsLocalRing IsDiscreteValuationRing

namespace GlobalTheory

namespace OrderNorm

theorem length_quot_ringEquiv {T U : Type*} [CommRing T] [CommRing U] (e : T ≃+* U) (x : T) :
    Module.length T (T ⧸ Ideal.span {x}) = Module.length U (U ⧸ Ideal.span {e x}) := by
  let _ : Algebra T U := e.toRingHom.toAlgebra
  let f : T ≃ₐ[T] U := AlgEquiv.ofRingEquiv (f := e) (fun _ => rfl)
  have hI : Ideal.span {e x} = (Ideal.span {x}).map (f : T →+* U) := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  rw [(Ideal.quotientEquivAlg (Ideal.span {x}) (Ideal.span {e x}) f hI).toLinearEquiv.length_eq]
  exact Module.length_eq_of_surjective e.surjective

end OrderNorm

end GlobalTheory
