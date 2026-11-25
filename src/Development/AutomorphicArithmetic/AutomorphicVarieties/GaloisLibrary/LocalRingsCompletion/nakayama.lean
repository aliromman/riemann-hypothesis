module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdicCompletion.Functoriality
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.IsCharOneOfSubsingleton
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.PowerSeries.Basic
public import Formalism.SharedLemmas.PrecompleteFinite

@[expose] public section

open PowerSeries IsLocalRing UpperTheory.V.abelian₂
open IsDiscreteValuationRing (addVal)
open scoped Pointwise TensorProduct Topology

theorem UpperTheory.V.abelian₂.nakayama :
    ∀ (R : Type) [CommRing R] (I : Ideal R) [IsPrecomplete I R] (M : Type) [AddCommGroup M] [Module R M] [IsHausdorff I M],
      (∀ (r : ℕ) (s : Fin r → M), Submodule.span R (Set.range s) ⊔ I • (⊤ : Submodule R M) = ⊤ →
        Submodule.span R (Set.range s) = ⊤) ∧
      (Module.Finite R (M ⧸ I • (⊤ : Submodule R M)) → Module.Finite R M) := by
  intro R _ I _ M _ _ _
  have part1 : ∀ (r : ℕ) (s : Fin r → M), Submodule.span R (Set.range s) ⊔ I • (⊤ : Submodule R M) = ⊤ →
      Submodule.span R (Set.range s) = ⊤ := by
    intro r s hs
    have hsurj : Function.Surjective (Fintype.linearCombination R s) := by
      haveI := Formalism.SharedLemmas.isPrecomplete_fin_pi I r
      apply surjective_of_mkQ_comp_surjective (I := I)
      intro q
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      have hm : m ∈ Submodule.span R (Set.range s) ⊔ I • (⊤ : Submodule R M) := by
        rw [hs]; exact Submodule.mem_top
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hm
      rw [← Fintype.range_linearCombination, LinearMap.mem_range] at ha
      obtain ⟨c, rfl⟩ := ha
      refine ⟨c, ?_⟩
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]
      rw [Submodule.Quotient.eq]
      simpa using Submodule.neg_mem _ hb
    rw [← Fintype.range_linearCombination, LinearMap.range_eq_top]
    exact hsurj
  refine ⟨part1, ?_⟩
  intro hfin
  obtain ⟨r, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M ⧸ I • (⊤ : Submodule R M))
  choose t ht using fun i => Submodule.Quotient.mk_surjective (I • (⊤ : Submodule R M)) (s i)
  have hsup : Submodule.span R (Set.range t) ⊔ I • (⊤ : Submodule R M) = ⊤ := by
    rw [sup_comm, ← Submodule.comap_map_mkQ, Submodule.map_span, ← Set.range_comp]
    have hcomp : (I • (⊤ : Submodule R M)).mkQ ∘ t = s := funext fun i => ht i
    rw [hcomp, hs, Submodule.comap_top]
  have htop := part1 r t hsup
  exact ⟨Submodule.fg_def.2 ⟨Set.range t, Set.finite_range t, htop⟩⟩
