module

public import Mathlib.Analysis.Complex.Norm
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EqOneOfPowNear
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

open Filter Topology

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test

theorem char_eq_one_of_near {G : Type} [AddCommGroup G] (H : AddSubgroup G) (χ : G → ℂ) (h0 : χ 0 = 1)
    (hχ : ∀ x y, χ (x + y) = χ x * χ y) (hs : ∀ x ∈ H, ‖χ x - 1‖ < 1 / 2) {x : G} (hx : x ∈ H) :
    χ x = 1 := by
  have hn : ∀ n : ℕ, χ (n • x) = χ x ^ n := by
    intro n
    induction n with
    | zero => simp [h0]
    | succ n ih => rw [succ_nsmul, hχ, ih, pow_succ]
  refine _root_.UpperTheory.Reformulated.B.EqOneOfPowNear.eq_one_of_pow_near _ fun n => ?_
  rw [← hn]
  exact hs _ (H.nsmul_mem hx n)

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
