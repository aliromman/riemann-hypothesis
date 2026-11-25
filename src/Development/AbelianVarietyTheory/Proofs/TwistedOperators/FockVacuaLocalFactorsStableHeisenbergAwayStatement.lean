module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVacuaLocalFactorsStableHeisenbergAway
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder


theorem _root_.GlobalTheory.T.fockVacua_localFactors_stable_heisenberg_away : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsStdChar D ψ (-1) → IsInfFam θ → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → (∀ (q : Place D) (w : WO S T), wAt q w = 0 → VacAt ψ θ S T sS sT ΛS ΛT q f → VacAt ψ θ S T sS sT ΛS ΛT q (heisO ψ S T w f)) ∧ ∀ (p : Place D), IsLocal ψ θ S T sS sT ΛS ΛT p f → (∀ w : WO S T, IsLocal ψ θ S T sS sT ΛS ΛT p (heisO ψ S T (wAt p w) f)) ∧ (∀ (c : ℂ) g, IsLocal ψ θ S T sS sT ΛS ΛT p g → IsLocal ψ θ S T sS sT ΛS ΛT p (c • f + g)) ∧ ∀ τ : D.what₂.Tau, p = .inr τ → ∀ z, IsLocal ψ θ S T sS sT ΛS ΛT p (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) := by
  first | exact @GlobalTheory.PlaceStable.heis_stable
