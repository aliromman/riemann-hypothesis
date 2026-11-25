module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormLtOne
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

theorem UpperTheory.Reformulated.B.MonicNormLtOne.mc_norm_lt :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {R : Type}
    [inst_1 : CommRing R] [inst_2 : IsLocalRing R] [inst_3 : Algebra ℤ_[l] R] (y : R →ₐ[ℤ_[l]] PadicAlgCl l),
    ∀ a ∈ IsLocalRing.maximalIdeal R, ‖(y : R → PadicAlgCl l) a‖ < (1 : ℝ) := by
  intro l _ R _ _ _ y a ha
  exact UpperTheory.Reformulated.B.NormLtOne.norm_lt_one (O := ℤ_[l]) y a ha
