module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
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

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.ptChart_of :
    PtChart := by
  intro Y V hV κ _
  refine ⟨?_, ?_, ?_⟩
  · intro f g hfg
    unfold ptOf at hfg
    have h := Spec.map_injective ((cancel_mono hV.fromSpec).mp hfg)
    exact congrArg CommRingCat.Hom.hom h
  · intro φ f m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [Function.iterate_succ_apply', ih, pow_succ']
      unfold twist ptOf
      rw [← Spec.map_comp_assoc]
      rfl
  · intro Z r W hW h B _ ρ z
    unfold ptOf
    rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec r hV hW h, ← Spec.map_comp_assoc,
      ← Spec.map_comp_assoc]
    rfl
