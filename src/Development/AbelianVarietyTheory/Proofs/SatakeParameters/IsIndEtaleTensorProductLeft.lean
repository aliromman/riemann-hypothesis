module

public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec
import Mathlib.CategoryTheory.Limits.Shapes.Countable
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

@[expose] public section

open CategoryTheory

namespace GlobalTheory

theorem isIndEtale_tensorProduct_left (C A M : Type) [CommRing C] [CommRing A] [CommRing M]
    [Algebra C A] [Algebra C M] (h : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap C A)) :
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap M (TensorProduct C M A)) := by
  haveI : (RingHom.toMorphismProperty @RingHom.Etale).IsStableUnderCobaseChange :=
    RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.2
      RingHom.Etale.isStableUnderBaseChange
  exact MorphismProperty.of_isPushout (P := MorphismProperty.ind.{0}
    (RingHom.toMorphismProperty @RingHom.Etale))
    (CommRingCat.isPushout_tensorProduct C M A) h

end GlobalTheory
