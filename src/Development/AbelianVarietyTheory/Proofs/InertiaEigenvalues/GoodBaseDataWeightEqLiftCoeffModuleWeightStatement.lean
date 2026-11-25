module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
public import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodBaseDataWeightEqLiftCoeffModuleWeight
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open Formalism.IndefR.Links
open scoped TensorProduct

theorem _root_.GlobalTheory.T.good_baseData_weight_eq_lift_coeff_module_weight : ∀ (D : D7) (T0 : Type) (L : LevCh D T0) (μ0 : T0) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)), L.Is μ0 → B.Good → B.mu0 = L.mu0 ((j : ℕ) + 1) → (∀ τ, B.w.ap τ = aPl D j ((Wc D j).sig (tauE D τ)).1 τ) → (∀ τ, B.w.am τ = aMi D j ((Wc D j).sig (tauE D τ)).1 ((Wc D j).sig (tauE D τ)).2 τ) → B.w.lam = FWT.lamV D j := by
  first | exact @GlobalTheory.BaseLiftWeight.lam_eq
