module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocHomAlgebraMap
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

open IsLocalRing



namespace GlobalTheory

noncomputable def tensorIntegralClosureInclusion (S L D : Type) [CommRing S] [Field L] [Algebra S L]
    [CommRing D] [Algebra S D] :
    integralClosure S L →ₐ[S] integralClosure D (TensorProduct S D L) where
  toRingHom := GlobalTheory.AbhyankarLocal.toNorm S L D
  commutes' s := by
    ext
    change (1 : D) ⊗ₜ[S] (algebraMap S L s) = _
    exact (Algebra.TensorProduct.includeRight (R := S) (A := D) (B := L)).commutes s

noncomputable instance instAlgebraIntegralClosureTensor (S L D : Type) [CommRing S] [Field L]
    [Algebra S L] [CommRing D] [Algebra S D] :
    Algebra (integralClosure S L) (integralClosure D (TensorProduct S D L)) :=
  (GlobalTheory.AbhyankarLocal.toNorm S L D).toAlgebra

instance (S L D : Type) [CommRing S] [Field L] [Algebra S L] [CommRing D] [Algebra S D] :
    IsScalarTower S (integralClosure S L) (integralClosure D (TensorProduct S D L)) :=
  IsScalarTower.of_algebraMap_eq fun s =>
    ((tensorIntegralClosureInclusion S L D).commutes s).symm

theorem algebraMap_integralClosure_tensor_eq (S L D : Type) [CommRing S] [Field L]
    [Algebra S L] [CommRing D] [Algebra S D] :
    algebraMap (integralClosure S L) (integralClosure D (TensorProduct S D L)) =
      GlobalTheory.AbhyankarLocal.toNorm S L D := rfl

end GlobalTheory
