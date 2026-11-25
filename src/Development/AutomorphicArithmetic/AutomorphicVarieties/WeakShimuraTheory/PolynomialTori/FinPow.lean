module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.nakayama
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FinitelyGeneratedModPow
public import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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

open IsLocalRing

theorem UpperTheory.V.Ws.Po.finPow {O A : Type} [CommRing O] [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O]
    [CommRing A] [IsLocalRing A] [Algebra O A] [IsNoetherianRing A]
    (hloc : (maximalIdeal O).map (algebraMap O A) ≤ maximalIdeal A)
    (hres : ∀ x : A, ∃ a : O, x - algebraMap O A a ∈ maximalIdeal A) (n : ℕ)
    (hn : maximalIdeal A ^ n ≤ (maximalIdeal O).map (algebraMap O A)) : Module.Finite O A := by
  haveI : IsHausdorff (maximalIdeal A) A := IsHausdorff.of_isLocalRing _ _ (maximalIdeal.isMaximal A).ne_top
  haveI : IsHausdorff (maximalIdeal O) A := IsHausdorff.of_map hloc
  refine (UpperTheory.V.abelian₂.nakayama O (maximalIdeal O) A).2 ?_
  obtain ⟨N, hN, hx⟩ := _root_.UpperTheory.Reformulated.B.FinitelyGeneratedModPow.fg_mod_pow (maximalIdeal A) hres n
  have : N.map (maximalIdeal O • (⊤ : Submodule O A)).mkQ = ⊤ := by
    rw [Submodule.map_mkQ_eq_top, eq_top_iff]
    intro x _
    obtain ⟨y, hy, h1⟩ := hx x
    have h2 : x - y ∈ maximalIdeal O • (⊤ : Submodule O A) := by
      rw [Ideal.smul_top_eq_map]
      exact hn h1
    have := Submodule.add_mem_sup h2 hy
    rwa [sub_add_cancel] at this
  exact ⟨this ▸ hN.map _⟩
