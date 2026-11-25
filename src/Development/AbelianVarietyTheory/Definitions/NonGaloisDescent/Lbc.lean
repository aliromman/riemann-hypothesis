module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsOrbitProd
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsLevelProjLevelProj
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

open NumberField IsDedekindDomain ValuativeRel
open GlobalTheory.LocGL

namespace GlobalTheory.FunExt

def lbc : BCRel := fun K L _ _ _ _ _ v u x X =>
  ∃ f : v.adicCompletion K →+* u.adicCompletion L, Continuous f ∧
    (∀ z : K, f (algebraMap K _ z) = algebraMap L _ (algebraMap K L z)) ∧
    letI : Algebra (v.adicCompletion K) (u.adicCompletion L) := f.toAlgebra
    ∀ s : u.adicCompletion L ≃ₐ[v.adicCompletion K] u.adicCompletion L, s ≠ 1 → GlobalTheory.LBC.IsLBCCl s x X

end GlobalTheory.FunExt

end
