module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.CoreSt
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

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw

def EquivLift : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c : ℝ), 0 < c → ∀ (R : Finset (Fin m → ℕ)) (t : Module.End ℂ (PX m n)),
    (∀ f ∈ box ε (R : Set _), t f ∈ box ε (R : Set _)) →
    (∀ i j, ∀ f ∈ box ε (R : Set _), t (KopL ε i j f) = KopL ε i j (t f)) →
    ∃ w ∈ Algebra.adjoin ℂ (Set.range fun ab : Fin m × Fin m => firstFamilyOperatorEnd (n := n) ε c ab.1 ab.2), ∀ f ∈ box ε (R : Set _), t f = w f

end PositivityTheory.Rg.Sw.LC
