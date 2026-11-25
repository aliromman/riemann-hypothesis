module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
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

namespace GlobalTheory.Published

open NumberField GlobalTheory.FieldSize

def WeberRayFieldSt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Algebra K ℂ], Module.finrank ℚ K = 2 → discr K < -4 →
    ∀ L : PeriodPair, (∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, algebraMap K ℂ (a : K) = z) → ∀ n : ℕ, 0 < n →
      ∃ (_ : NumberField (IntermediateField.adjoin K (weberSet L n)))
        (_ : IsAbelianGalois K (IntermediateField.adjoin K (weberSet L n))),
        IsRay (IntermediateField.adjoin K (weberSet L n)) (Ideal.span {(n : 𝓞 K)})

end GlobalTheory.Published
