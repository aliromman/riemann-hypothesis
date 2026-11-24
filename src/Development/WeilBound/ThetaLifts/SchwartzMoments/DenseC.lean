module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.DenseHasCompactSupport
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.RingTheory.SimpleRing.Principal
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

noncomputable section

namespace PositivityTheory.ThKOwn

open scoped SchwartzMap

theorem dense_compactSupport {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    Dense {f : 𝓢(V, ℂ) | HasCompactSupport (f : V → ℂ)} := by
  let e : V ≃L[ℝ] (Fin (Module.finrank ℝ V) → ℝ) := (Module.finBasis ℝ V).equivFunL
  let P := SchwartzMap.compCLMOfContinuousLinearEquiv (F := ℂ) ℂ e
  let Q := SchwartzMap.compCLMOfContinuousLinearEquiv (F := ℂ) ℂ e.symm
  have hPQ : ∀ f, P (Q f) = f := fun f => by ext x; simp [P, Q]
  have hr : DenseRange P := Function.Surjective.denseRange fun f => ⟨Q f, hPQ f⟩
  refine (hr.dense_image P.continuous (GlobalTheory.CompanionTheory.DiracComb.dense_hasCompactSupport _)).mono ?_
  rintro _ ⟨f, hf, rfl⟩
  exact HasCompactSupport.comp_homeomorph hf e.toHomeomorph

end PositivityTheory.ThKOwn

end
