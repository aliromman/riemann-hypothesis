module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSymplecticBasisToMatrixOffDiagDvd
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
import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory

theorem specialLinearGroup_map_intCast_zmod_surjective :
    ∀ (M : ℕ), Function.Surjective (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) :
      SL(2, ℤ) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod M)) :=
  fun M => GlobalTheory.specialLinearGroup_map_zmod_surjective (Fin 2) M

end GlobalTheory
