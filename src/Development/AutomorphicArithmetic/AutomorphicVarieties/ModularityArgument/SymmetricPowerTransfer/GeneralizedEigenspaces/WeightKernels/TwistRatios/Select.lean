module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.IsLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.Wcount
import Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeD
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

theorem UpperTheory.V.Z.Sym.Ga.select :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (X : Set (Plc L)), ∃ P ⊆ X, Set.InjOn (fun w : Plc L => w.under (𝓞 (Lp L))) P ∧ ∀ w ∈ X, ∃ w' ∈ P, w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L)) := by
  intro L _ _ _ X
  rcases isEmpty_or_nonempty (Plc L) with hE | hN
  · refine ⟨∅, Set.empty_subset _, Set.injOn_empty _, ?_⟩
    intro w
    exact (IsEmpty.false w).elim
  set f : Plc L → _ := fun w : Plc L => w.under (𝓞 (Lp L)) with hf
  have spec : ∀ w ∈ X, Classical.epsilon (fun v => v ∈ X ∧ f v = f w) ∈ X ∧
      f (Classical.epsilon (fun v => v ∈ X ∧ f v = f w)) = f w :=
    fun w hw => Classical.epsilon_spec (p := fun v => v ∈ X ∧ f v = f w) ⟨w, hw, rfl⟩
  refine ⟨(fun w => Classical.epsilon (fun v => v ∈ X ∧ f v = f w)) '' X, ?_, ?_, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact (spec w hw).1
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    have hab' : f a = f b := by
      have := hab
      simp only at this
      rw [(spec a ha).2, (spec b hb).2] at this
      exact this
    simp only [hab']
  · intro w hw
    exact ⟨_, ⟨w, hw, rfl⟩, (spec w hw).2⟩
