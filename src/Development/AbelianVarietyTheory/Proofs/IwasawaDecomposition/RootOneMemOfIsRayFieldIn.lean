module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassNumberDvdHstar
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.Mem.RayRoots

theorem rootOne_mem_of_isRayFieldIn : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (φ : E →+* ℂ)
    (N n : ℕ) (M : IntermediateField ℚ ℂ), N ≠ 0 → n ∣ N → IsRayFieldIn φ (natIdeal E N) M → rootOne n ∈ M :=
  fun _ _ _ _ φ _ _ _ hN hn hM => GlobalTheory.Mem.FieldsEx.rootOne_mem_ray φ hN hn hM

end GlobalTheory.Mem.RayRoots
