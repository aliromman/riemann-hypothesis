module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HxiTZeroComb
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperEighthFibrePowerOver
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.EtC GlobalTheory.UPel.HT GlobalTheory.PELU GlobalTheory.KS
open scoped TensorProduct Matrix

namespace GlobalTheory.KS.Leray

theorem isProper_pow_hom {S : Scheme.{0}} (A : Over S) (hA : IsProper A.hom) (m : ℕ) :
    IsProper (GlobalTheory.KS.pow A m).hom :=
  GlobalTheory.FibrePowerProper.isProper_fan_pt m (fun _ => A) (fun _ => hA) (limit.cone _) (limit.isLimit _)

end GlobalTheory.KS.Leray
