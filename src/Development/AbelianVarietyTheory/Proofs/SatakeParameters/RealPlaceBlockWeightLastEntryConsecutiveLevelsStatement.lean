module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealPlaceBlockWeightLastEntryConsecutiveLevels
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

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA

theorem _root_.GlobalTheory.T.realPlaceBlockWeightLastEntry_consecutive_levels : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (j : ℕ) (τ : D.what₂.Tau), (eT X D pos j τ = if IsOddPos (pos.symm τ).2 then wT X D pos j τ - cT1 X D pos j τ else X.nuv (pos.symm τ).1 (j + 1) (pos.symm τ).2 (NN X.G.P.m X.t j) - wT X D pos j τ) ∧ (eT X D pos (j + 1) τ = if IsOddPos (pos.symm τ).2 then wT X D pos j τ - cT1 X D pos j τ else -wT X D pos j τ) := by
  first | exact @GlobalTheory.TwV.DelA.eT_last_pair
