module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.Basic.Complex.Basic
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace PositivityTheory.Lbc

def IsHeckeOpG {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V) (K : Subgroup G)
    (g : G) (T : Module.End ℂ (fixed π K)) : Prop :=
  ∀ (v : fixed π K) (f : Module.Dual ℂ V), (∀ x ∈ K, f ∘ₗ π x = f) → f (π g (v : V)) = f ((T v : fixed π K) : V)

def HeckeExistsUnique : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) →
    IsCompact (K : Set G) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π →
      ∀ g : G, ∃! T : Module.End ℂ (fixed π K), IsHeckeOpG π K g T

end PositivityTheory.Lbc

end
