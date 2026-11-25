module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.RingHom.Etale
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.SSG

def ChartAt {O : Type} [CommRing O] (ϖ : O) {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of O)) (x : X) : Prop :=
  ∃ (U : X.Opens) (_ : IsAffineOpen U) (_ : x ∈ U) (m r : ℕ) (_ : 1 ≤ r) (_ : r ≤ m)
    (ψ : (MvPolynomial (Fin m) O ⧸ Ideal.span (Set.singleton
      ((∏ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < r), MvPolynomial.X i) -
        MvPolynomial.C ϖ))) →+* Γ(X, U)),
    ψ.Etale ∧ ψ.comp (algebraMap O _) = ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ p.appLE ⊤ U le_top).hom

end GlobalTheory.SSG

end
