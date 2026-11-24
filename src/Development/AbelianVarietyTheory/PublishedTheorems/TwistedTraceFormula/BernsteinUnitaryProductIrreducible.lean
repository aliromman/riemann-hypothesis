module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
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
import Mathlib.Topology.Algebra.Group.Units

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.Published

def BernsteinUnitaryProductIrreducible : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (r t : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W),
    IsSmooth π₁ → π₁.IsIrreducible → IsUnitarisable π₁ →
    IsSmooth π₂ → π₂.IsIrreducible → IsUnitarisable π₂ →
    (prod₂ π₁ π₂).IsIrreducible

namespace BernsteinUnitaryProductIrreducible

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem detRep_hyp (t : ℕ) {χ : kˣ →* ℂˣ} (hs : IsSmoothChar χ) (hu : IsUnitaryChar χ) :
    IsSmooth (detRep (Fin t) χ) ∧ (detRep (Fin t) χ).IsIrreducible ∧
      IsUnitarisable (detRep (Fin t) χ) :=
  ⟨(isSmooth_ofChar_iff _).2 hs.detChar, isIrreducible_ofChar _,
    (isUnitarisable_ofChar_iff _).2 fun _ => hu _⟩

theorem prod₂_detRep (H : BernsteinUnitaryProductIrreducible) {r : ℕ} (t : ℕ)
    {π : Representation ℂ (GL (Fin r) k) V} (s : IsSmooth π) (i : π.IsIrreducible)
    (u : IsUnitarisable π) {χ : kˣ →* ℂˣ} (hs : IsSmoothChar χ) (hu : IsUnitaryChar χ) :
    (prod₂ π (detRep (Fin t) χ)).IsIrreducible :=
  have h := detRep_hyp t hs hu
  H k r t V ℂ π _ s i u h.1 h.2.1 h.2.2

end BernsteinUnitaryProductIrreducible

end GlobalTheory.Published
