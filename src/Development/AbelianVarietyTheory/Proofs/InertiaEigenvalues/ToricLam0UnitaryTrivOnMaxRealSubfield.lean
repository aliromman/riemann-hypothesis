module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
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

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie

theorem delAt_unitary_triv {D : D7} (C : CharFrame D) (l : ℕ) : (C.delAt l).IsUnitary ∧ (C.delAt l).TrivOn D.host.F := by
  unfold CharFrame.delAt
  split_ifs
  · exact ⟨C.isDel'.unitary, C.isDel'.triv⟩
  · exact ⟨C.isDel.unitary, C.isDel.triv⟩

theorem toricLam0_unitary_trivOnMaxRealSubfield : ∀ (D : D7) (Z : LamDat D), Z.Ok → ∀ (l : ℕ) (j a : Fin D.R.m),
    (Z.lam0 l j a).IsUnitary ∧ TrivOnF (Z.lam0 l j a) := by
  intro D Z h l j a
  have hd := delAt_unitary_triv Z.C l
  exact ⟨((Z.C.isMu0 j).unitary.mul hd.1).mul (h.aux a).unitary.inv,
    ((Z.C.isMu0 j).triv.mul hd.2).mul (h.aux a).triv.inv⟩

end GlobalTheory.LamTie
