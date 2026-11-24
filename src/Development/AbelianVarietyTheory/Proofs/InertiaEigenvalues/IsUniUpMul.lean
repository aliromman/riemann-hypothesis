module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWhittakerDatumAndHalfLevels
public import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
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

namespace GlobalTheory.UnipotentUpperMul

theorem isUniUp_mul : ∀ {R : Type} [inst : CommRing R] {N : ℕ} {M M' : Matrix (Fin N) (Fin N) R},
    Formalism.MainNotions.ArithmeticCylinders.IsUniUp M → Formalism.MainNotions.ArithmeticCylinders.IsUniUp M' → Formalism.MainNotions.ArithmeticCylinders.IsUniUp (M * M') := by
  apply GlobalTheory.BadCount.Inh.isUniUp_mul

end GlobalTheory.UnipotentUpperMul
