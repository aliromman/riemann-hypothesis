module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
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

namespace GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceUnitaryEvaluation

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct

section Notions

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def evalAt (v : HeightOneSpectrum (𝓞 F)) : FiniteAdeleRing (𝓞 F) F →ₐ[F] v.adicCompletion F where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl


variable (E) in
def loc (v : HeightOneSpectrum (𝓞 F)) : RA F E →ₐ[F] v.adicCompletion F ⊗[F] E :=
  Algebra.TensorProduct.map (evalAt v) (AlgHom.id F E)



variable (E) in
def IsSplitPlace (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∃ w w' : Ideal (𝓞 E), w ≠ w' ∧ w.IsPrime ∧ w'.IsPrime ∧
    w.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal ∧ w'.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal

end Notions

section Basic₂

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceUnitaryEvaluation
