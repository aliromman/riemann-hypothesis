module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDataDistinctPlacesCommute
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix GlobalTheory.FinPl GlobalTheory.SplitWeil ValuativeRel

theorem _root_.GlobalTheory.T.splitPlaceData_distinct_places_commute : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p p' : SplitPt D k) (n n' m m' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype m]
    [DecidableEq m] [Fintype m'] [DecidableEq m'] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA →
    p'.UnitAA → p.v ≠ p'.v → ∀ (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (α' : Frame p' S m')
    (β' : Frame p' T m) (LS : Lat S) (LT : Lat T) (f₀ g h : WO S T → ℂ) (Ψ : Matrix n n' k → ℂ)
    (Ψ' : Matrix m m' k → ℂ), Vac ψ S T LS LT (· = p'.v) f₀ → Over ψ α β LS LT f₀ Ψ g →
      Over ψ α' β' LS LT g Ψ' h → ∃ g', Over ψ α' β' LS LT f₀ Ψ' g' ∧ Over ψ α β LS LT g' Ψ h := by
  first | exact @GlobalTheory.FinPl.overSwap
