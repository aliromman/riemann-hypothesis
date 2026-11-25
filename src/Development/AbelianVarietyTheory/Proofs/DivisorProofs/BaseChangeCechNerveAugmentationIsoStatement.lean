module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeCechNerveAugmentationIso
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

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.baseChange_cechNerveAugmentation_iso : ∀ (S W V : Scheme.{0}) (r : W ⟶ S) (f : V ⟶ W) (U : Over S), ∃ (e₁ : cech (pullback.snd f (pullback.fst r U.hom)) ≅ (bc (cechAug f ≫ sch.map r)).obj U) (e₂ : sch.obj (pullback r U.hom) ≅ (bc (sch.map r)).obj U), e₁.hom ≫ (bcMap (cechAug f) (sch.map r)).app U = cechAug _ ≫ e₂.hom := by
  first | (exact @GlobalTheory.EtC.bc_cechAug_iso)
