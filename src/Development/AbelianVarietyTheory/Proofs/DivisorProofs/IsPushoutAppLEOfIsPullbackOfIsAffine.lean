module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Tactic.Linter.HaveILetI
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.AffBaseChange

theorem isPushout_appLE_of_isPullback_of_isAffine :
    ∀ (X X' S S' : Scheme.{0}) (f : X' ⟶ X) (g : X' ⟶ S') (p : X ⟶ S) (q : S' ⟶ S),
      IsPullback f g p q → IsAffine S → IsAffine S' → ∀ (W : X.Opens), IsAffineOpen W →
      IsPushout (p.appLE ⊤ W (fun _ _ => trivial)) q.appTop (f.app W)
        (g.appLE ⊤ (f ⁻¹ᵁ W) (fun _ _ => trivial)) := by
  intro X X' S S' f g p q h hS hS' W hW
  haveI : IsAffineHom q := inferInstance
  have P := ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.isPushout_appLE h.flip this (isAffineOpen_top S) hW
    (fun _ _ => trivial) (fun _ _ => trivial)
  exact P.flip

end GlobalTheory.AffBaseChange
