module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
import Mathlib.RingTheory.PiTensorProduct
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

open Matrix Finset
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.RealCount.KHw

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)

variable {n : ℕ}

section

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)} {Kf : Fin n → Fin n → Module.End ℂ V}

theorem glRel_kF {E1 E2 : Fin n → Fin n → Module.End ℂ V} (h : IsPair E1 E2) : Formalism.REAL.GlRel (kF E1 E2) := by
  intro a b c d
  have h1 := h.gl1 a b c d
  have h2 := h.gl2 a b c d
  have c1 := h.comm a b c d
  have c2 := h.comm c d a b
  have key : kF E1 E2 a b * kF E1 E2 c d - kF E1 E2 c d * kF E1 E2 a b =
      (E1 a b * E1 c d - E1 c d * E1 a b) + (E2 a b * E2 c d - E2 c d * E2 a b) := by
    simp only [kF, add_mul, mul_add, c1, ← c2]
    abel
  rw [key, h1, h2]
  simp only [kF]
  split_ifs <;> abel

end

end GlobalTheory.CompanionTheory.RealCount.KHw
