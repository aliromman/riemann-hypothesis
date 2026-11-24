module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.ColMatMulGlEmbMat
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
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

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil

namespace GlobalTheory.BZSeg

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def DerivJac : Prop :=
  ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n j : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin (n + 1 + j + 1)) k) V), IsSmooth π → HasFiniteLength π →
    ∀ S : IrrRep (GL (Fin (n + 1)) k), IsSubquotient S.ρ (GlobalTheory.BZMir.deriv k ψ j π) →
      ∃ (β : IrrGL (k := k)) (hd : ∑ a, (![(IrrGL.of S.ρ S.smooth S.irr).nu (-(((j : ℂ) + 1) / 2)), β] a).1 = n + 1 + j + 1),
        β.1 = j + 1 ∧ 1 ≤ Zc.jm ![(IrrGL.of S.ρ S.smooth S.irr).nu (-(((j : ℂ) + 1) / 2)), β] hd π

def JmTheta : Prop :=
  ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π →
    HasFiniteLength π → ∀ (a b : IrrGL (k := k)) (hd : ∑ i, (![a, b] i).1 = N)
      (hd' : ∑ i, (![Zc.dualCl b, Zc.dualCl a] i).1 = N),
      Zc.jm ![a, b] hd (π.comp (Zc.Cos.thetaW k N)) = Zc.jm ![Zc.dualCl b, Zc.dualCl a] hd' π

end GlobalTheory.BZSeg

end
