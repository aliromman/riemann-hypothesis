module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
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

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.BasicNotions Formalism.MainNotions.N

namespace GlobalTheory.DefiniteBC

attribute [local instance] host_isCMField

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂}
variable {A : NAut N}

def CuspReadG (rc : RecMap A) : Prop :=
  ∀ (a : ℕ) (P : CuspSub H.E a), 1 ≤ a → P.IsCsd →
    (∀ w (σ : LocIrr w a), P.IsLocComp w σ → UpperTheory.Zero.LLC.Good (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred)) →
    ∃ π : A.CG a, A.csd π ∧ (∀ w σ, P.IsLocComp w σ → A.locG π w = rc w a σ) ∧ ∀ τ m, P.HasInfChar τ m → A.infG π τ = m

end GlobalTheory.DefiniteBC

end
