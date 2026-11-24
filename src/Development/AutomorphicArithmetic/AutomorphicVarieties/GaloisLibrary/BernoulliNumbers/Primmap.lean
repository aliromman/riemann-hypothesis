module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Condmap
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

open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_primmap :
    ∀ {R S : Type} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S] {N : ℕ} [NeZero N] (f : R →+* S), Function.Injective f → ∀ (k : ℕ) (χ : DirichletCharacter R N), f (Bprim k χ) = Bprim k (χ.ringHomComp f) := by
  intro R S _ _ _ _ N _ f hf k χ
  obtain ⟨hcond, hval, -⟩ := b_condmap f hf χ

  rw [Bprim_eq, Bprim_eq, hcond, map_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [map_mul, hval a, RingHom.map_rat_algebraMap]
