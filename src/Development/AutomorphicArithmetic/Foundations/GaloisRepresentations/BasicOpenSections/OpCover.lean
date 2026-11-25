module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsWtZero
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCorrOpOfAvg
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.GenericMulOfProd

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt)
open UpperTheory.Gal.crystallineComparison (PtId fn)

namespace UpperTheory.Gal.Mod

def OpCover : Prop := ∀ (l : ℕ) [Fact l.Prime] {S S' : Scheme.{0}} (c c' : TranscendenceTraces.Corr S S') (u : c.Z ⟶ c'.Z) [IsFinite u] (δ : ℕ),
  c.w = Wt.const _ 1 → c'.w = Wt.const _ 1 → u ≫ c'.p = c.p → u ≫ c'.f = c.f → IsUnit (l : Γ(S, ⊤)) →
  (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : gp Ω ⟶ c'.Z), (fib u x).ncard = δ) →
  ∀ k i : ℤ, c.opQ l k i = (δ : ℚ_[l]) • c'.opQ l k i

end UpperTheory.Gal.Mod

end
