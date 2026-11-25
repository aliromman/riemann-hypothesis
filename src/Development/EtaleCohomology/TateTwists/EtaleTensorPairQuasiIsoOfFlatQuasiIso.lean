module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
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

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleTensorPairQuasiIsoOfFlatQuasiIso : Prop :=
  ∀ (R : Type) [CommRing R] {I I' J T T' : Cx R} [I.IsStrictlyGE 0] [I'.IsStrictlyGE 0] [J.IsStrictlyGE 0] (τ : Pair I J T) (τ' : Pair I' J T'), τ.IsTensor → τ'.IsTensor → (∀ t, FlatS (J.X t)) → ∀ (f : I ⟶ I') [QuasiIso f] (u : T ⟶ T'), τ.Compat τ' f (𝟙 J) u → QuasiIso u
