module

public import Mathlib.FieldTheory.Separable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeftMulMatrixTransfer
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

open Polynomial Matrix Formalism.UG

namespace GlobalTheory.SepCharpoly

theorem charpoly_dvd_of_aeval_eq_zero :
    ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (M : Matrix (Fin n) (Fin n) R) (p : R[X]),
      M.charpoly.Separable → aeval M p = 0 → M.charpoly ∣ p := by
  intro R _ _ n M p hs hp
  classical
  let K := FractionRing R
  let f : R →+* K := algebraMap R K
  have hf : Function.Injective f := IsFractionRing.injective R K
  rw [← Polynomial.map_dvd_map f hf M.charpoly_monic, ← Matrix.charpoly_map]
  refine GlobalTheory.ClassParam.charpoly_dvd_of_aeval (M.map f) ?_ (p.map f) ?_
  · rw [Matrix.charpoly_map]; exact hs.map
  · rw [show M.map f = (f.mapMatrix : Matrix (Fin n) (Fin n) R →+* _) M from rfl]
    have := congrArg (AlgHom.mapMatrix (m := Fin n) (Algebra.ofId R K)) hp
    rw [← aeval_algHom_apply, map_zero] at this
    rw [aeval_map_algebraMap]
    exact this

end GlobalTheory.SepCharpoly
