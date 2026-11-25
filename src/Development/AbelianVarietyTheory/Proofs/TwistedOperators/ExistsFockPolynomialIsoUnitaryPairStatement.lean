module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChosenSeries
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.BarMatrix
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFockPolynomialIsoUnitaryPair
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace

theorem _root_.GlobalTheory.T.exists_fockPolynomialIso_unitaryPair : ∀ (p q r s a b : ℕ) (ε : Fin a → Bool) (ε' : Fin b → Bool) (e : Ix p q ≃ Fin a) (e' : Ix r s ≃ Fin b), GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.SignCompat ε e → GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.SignCompat ε' e' → ∃ κ : LPol b a ≃ₗ[ℂ] Pol p q r s, IsPolyIso ε ε' e e' κ := by
  first | exact @GlobalTheory.Chain.RealIt.PolyIso.exists_isPolyIso
