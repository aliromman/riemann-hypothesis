module

public import Formalism.SharpRestriction.GlobalSchurBounds.TaylorLogMetric
public import Formalism.LocalRingCardinality.DataForced
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

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric Classical

namespace GlobalTheory.KerStd

def StdBases (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {N : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) : Prop :=
  (∀ τ, LocBasisW D (tauEmb D lam τ) L (P τ)) ∧
  ((IsResidueClassZero D p ∨ IsSg D p) → ∀ z : Bool × HH D,
    ((P (tauPl D (posPl D p z 1))).map D.host.conj).transpose * P (tauPl D z) = 1) ∧
  (p = D.host.d → DualB D P)

def stdSer (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {N N' : ℕ} (κ : D.what₂.Tau → ℂ_[p])
    (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E)
    (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) : MvPowerSeries ((Bool × HH D) × Fin N × Fin N') ℂ_[p] :=
  atLin (fun k (j : (Bool × HH D) × Fin N × Fin N') =>
    κ k.1 * chgB D lam P P' k ((0 : ZMod 1), (tauPl D j.1, j.2))) (fun j => MvPowerSeries.X j) F

end GlobalTheory.KerStd
