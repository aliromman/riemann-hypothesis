module

public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic
import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Shapiro
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
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PermRepSingle

@[expose] public section

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab

theorem isZero_groupHomology_succ_of_projective : ∀ (k G : Type) [CommRing k] [Group G] (P : Rep k G), Projective P → ∀ n : ℕ, IsZero (groupHomology P (n + 1)) := by
  intro k G _ _ P hP n
  classical
  let S : Subgroup G := ⊥
  let B : Rep k S := Rep.res S.subtype P
  let adj := Rep.indResAdjunction k S.subtype
  let ε : (Rep.indFunctor k S.subtype).obj B ⟶ P := adj.counit.app P
  have hε : Epi ε := by
    rw [Rep.epi_iff_surjective]
    intro x
    refine ⟨(adj.unit.app B).hom x, ?_⟩
    have h2 := congrArg (fun f => f.hom x) (adj.right_triangle_components P)
    exact h2
  let s := Projective.factorThru (𝟙 P) ε
  have hs : s ≫ ε = 𝟙 P := Projective.factorThru_comp _ _
  have hZ : IsZero (groupHomology (Rep.ind S.subtype B) (n + 1)) :=
    (isZero_groupHomology_succ_of_subsingleton B n).of_iso
      (groupHomology.indIso S B (n + 1))
  rw [IsZero.iff_id_eq_zero]
  have hid : (groupHomology.functor k G (n + 1)).map (s ≫ ε) = 𝟙 _ := by
    rw [hs]
    exact CategoryTheory.Functor.map_id _ _
  refine Eq.trans hid.symm ?_
  rw [CategoryTheory.Functor.map_comp,
    hZ.eq_of_tgt ((groupHomology.functor k G (n + 1)).map s) 0]
  exact zero_comp

end GlobalTheory.HomStab

