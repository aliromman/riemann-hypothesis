module

public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlgTAll
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.FinalEq
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
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero

@[expose] public section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

namespace GlobalTheory.MomEq

theorem eq_and_alg : (∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → B.EqP χ) ∧ (∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → ∀ t : VC D N N', (∃ a : ℕ, 0 < a ∧ a • t ∈ La D B.tor L L') → ∀ α, Formalism.MainNotions.TaylorLogMetric.taylor D (U D B.tor t (B.eNat χ N N' L L')) α ∈ Qbar) :=
  ⟨fun _ _ _ B χ hcc hδ hχ => Formalism.L2.PairingIndexBounds.Eq.SqG.eulerProduct_eq_of_curve_ideal B hcc hδ χ hχ,
   fun D cc δ B χ hcc hδ hχ => _root_.GlobalTheory.ThLoc.Alg.algTAll D cc δ B χ hcc hδ hχ⟩

end GlobalTheory.MomEq
