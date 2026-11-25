module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
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

open Polynomial Matrix

theorem UpperTheory.V.Pr.T.completeDVRExt :
    ∀ {A K L : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
      [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [Field K] [Algebra A K] [IsFractionRing A K] [Field L]
      [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L],
      Module.Finite A (integralClosure A L) ∧ IsDiscreteValuationRing (integralClosure A L) := by
  intro A K L _ _ _ _ _ _ _ _ _ _ _ _
  exact ⟨GlobalTheory.FormalIsogeny.finite_integralClosure A K L,
    GlobalTheory.FormalIsogeny.isDiscreteValuationRing_integralClosure A K L⟩
