module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.UnitaryDoubleCosetIndicator
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.FinFacts
import Mathlib.Tactic.Linter.HaveILetI
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

open ValuativeRel UpperTheory.V UpperTheory.V.Z.Sym

theorem UpperTheory.V.Z.Sym.Al.dcMap {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    (W : Sig.Lev k) {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (μ : Representation ℂ (GL (Fin n) k) M) (ν : Representation ℂ (GL (Fin n) k) N) (f : M →ₗ[ℂ] N)
    (hf : ∀ g x, f (μ g x) = ν g (f x)) (a : GL (Fin n) k) (v : M) :
    f (Hi.dc μ (W.J n) (W.J n) a v) = Hi.dc ν (W.J n) (W.J n) a (f v) := by
  classical
  have hJ := ((Sig.finFacts k W).2.2.2.2.2 n).1 a
  haveI := Set.Finite.to_subtype hJ
  haveI := Fintype.ofFinite (MulAction.orbit (W.J n) (a : GL (Fin n) k ⧸ W.J n))

  simp only [Hi.dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply, map_sum, hf]
