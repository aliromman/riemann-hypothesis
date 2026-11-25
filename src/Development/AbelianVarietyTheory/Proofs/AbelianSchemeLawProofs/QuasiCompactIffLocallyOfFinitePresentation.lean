module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G

namespace GlobalTheory.SemiAbelianCompare

section General

theorem geometricallyConnected_of_isAlgClosed {X S : Scheme.{u}} (f : X ⟶ S)
    (h : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ S),
      ConnectedSpace ↥(pullback f s)) : GeometricallyConnected f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ y => ?_⟩
  let b : Spec (CommRingCat.of (AlgebraicClosure K)) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
  have hb : Surjective b := ⟨fun z => ⟨_, Subsingleton.elim (b (default : PrimeSpectrum _)) z⟩⟩
  have := h _ (b ≫ y)
  let g := (pullbackLeftPullbackSndIso f y b).inv ≫ pullback.fst (pullback.snd f y) b
  exact g.surjective.connectedSpace g.continuous

end General

section Exact

variable {S : Scheme.{u}} {X : Type u} [AddCommGroup X] {G B : Over S} [GrpObj G] [GrpObj B]
  {i : Semi.splitTorus S X ⟶ G} {q : G ⟶ B}

end Exact

section Field

variable {k : Type u} [Field k] {G : Over (Spec (CommRingCat.of k))} [GrpObj G]


end Field

end GlobalTheory.SemiAbelianCompare

namespace GlobalTheory

open SemiAbelianCompare

end GlobalTheory
