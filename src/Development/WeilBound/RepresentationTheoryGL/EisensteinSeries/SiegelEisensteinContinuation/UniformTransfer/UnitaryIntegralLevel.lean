module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
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
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf

@[expose] public section

noncomputable section

open Matrix

namespace PositivityTheory.RgEis

variable {E R : Type} [Field E] [CommRing R]

namespace Ad

variable (A : Ad E R)

variable [TopologicalSpace R]

end Ad


open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

def eSF {F : Type} [Field F] [NumberField F] (S : Finset (Pl F)) : AF F :=
  LinearMap.inl F (Ainf F) (Af F) 1 + LinearMap.inr F (Ainf F) (Af F) (∑ v ∈ S, singleFin v 1)

end PositivityTheory.RgEis
