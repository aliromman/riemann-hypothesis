module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.MultiplicationKernelIdentity
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

open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity

noncomputable section
namespace GlobalTheory.HermitianPreEigenvalues
variable {O : Type} [CommRing O] {S : Type} [Fintype S] [DecidableEq S]

def mulR (a : S → O) (N : ℕ) (r : RS a) : (Fin N → RS a) →ₗ[O] (Fin N → RS a) :=
  (LinearMap.lsmul (RS a) (Fin N → RS a) r).restrictScalars O

def preEig (a : S → O) {N : ℕ} (Fil : Submodule (RS a) (Fin N → RS a)) (τ : S) :
    Submodule O (Fin N → RS a) :=
  (Fil.restrictScalars O).comap (mulR a N (lin a τ))

def filKer (a : S → O) {N : ℕ} (Fil : Submodule (RS a) (Fin N → RS a)) (τ : S) :
    Submodule O (Fin N → RS a) :=
  Fil.restrictScalars O ⊓ LinearMap.ker (mulR a N (cofac a τ))

end GlobalTheory.HermitianPreEigenvalues
