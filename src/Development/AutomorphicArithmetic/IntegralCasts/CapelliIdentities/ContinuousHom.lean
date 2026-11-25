module

public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Group.Defs
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

theorem UpperTheory.Reformulated.B.ContinuousHomomorphism.cont_hom :
    ∀ {Γ M : Type} [inst : Group Γ]
    [inst_1 : TopologicalSpace Γ] [ContinuousInv Γ] [inst_3 : Monoid M] [inst_4 : TopologicalSpace M] (f : Γ →* Mˣ),
    (Continuous fun (g : Γ) ↦ (↑((f : Γ → Mˣ) g) : M)) → Continuous (⇑f : Γ → Mˣ) := by
  intro Γ M _ _ _ _ _ f h
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  refine (h.comp continuous_inv).congr fun g => ?_
  simp only [Function.comp_apply, map_inv]
