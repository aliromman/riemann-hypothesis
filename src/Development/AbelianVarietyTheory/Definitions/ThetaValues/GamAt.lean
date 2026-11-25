module

public import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
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

namespace GlobalTheory.RunIn

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

def GamAt {D : D7} (T : Core D) : Prop :=
  ∀ j, InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp) (γ : GL (Fin D.R.r) D.host.E),
    IsUStab ((T.U j σ).X k).Gm ((T.U j σ).X k).Λ γ →
    (∀ x ∈ ((T.U j σ).X k).Λ, ∃ y ∈ ((T.U j σ).X k).Λ,
      Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) x - x = (T.Q.l.M : D.host.E) • y) →
    γ ∈ ((T.U j σ).X k).Γ

def l1At {K : Type} [Field K] {ι : Type} (σ : K →+* ℂ) (P : MvPolynomial ι K) : ℝ :=
  ∑ m ∈ P.support, ‖σ (P.coeff m)‖

end GlobalTheory.RunIn
