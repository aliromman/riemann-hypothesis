module

public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HdimEqZeroOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SameDiv

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.Div

theorem coh_subsingleton_of_cls_eq : ∀ (X : Scheme.{0}) (M N : LB X) (hM : M.IsLB) (hN : N.IsLB),
    cls M hM = cls N hN → ∀ q : ℕ, Subsingleton (coh (LB.toMod M) q) →
      Subsingleton (coh (LB.toMod N) q) := by
  intro X M N hM hN e q h
  obtain ⟨i⟩ := nonempty_twist_iso_of_cls_eq (structureModule X) hM hN e
  exact (cohOn.mapIso Γ(X, ⊤) ⊤ q
    ((Twist.unitTwistIso M).symm ≪≫ i ≪≫ Twist.unitTwistIso N)).toEquiv.subsingleton_congr.1 h

end GlobalTheory.Div
