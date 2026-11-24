module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LcountNorm
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

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Loc.datSmul : UpperTheory.V.Z.Sym.Loc.DatSmul := by
  intro K _ Δ τ c d m h t
  have hsig : sigL ((t : K) • m) = (t : K) • sigL m := by
    ext <;> simp [sigL]
  have hst : ∀ z : EL Δ τ, star ((t : K) • z) = (t : K) • star z := by
    intro z
    ext <;> simp
  refine ⟨h.reg, h.c_ne, h.d_norm, ?_, ?_, ?_⟩
  · rw [Algebra.smul_def]
    exact (t.isUnit.map (algebraMap K (EL Δ τ))).mul h.m_unit
  · rw [hsig, hst, h.m_star]
  · rw [hsig, h.m_sig, smul_mul_assoc, smul_mul_assoc]
