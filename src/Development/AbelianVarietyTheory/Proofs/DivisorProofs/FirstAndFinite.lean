module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.RingTheory.PiTensorProduct
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

namespace GlobalTheory.EtC

def firstAndFinite (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (k : ℕ) (F : Finset A) :
    Subalgebra R (PiTensorProduct R (fun _ : Fin (k + 1) => A)) :=
  Algebra.adjoin R (Set.range (PiTensorProduct.singleAlgHom (R := R) (A := fun _ : Fin (k + 1) => A) 0) ∪
    ⋃ i : Fin (k + 1), (PiTensorProduct.singleAlgHom (R := R) (A := fun _ : Fin (k + 1) => A) i) '' (F : Set A))

def firstIncl (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (k : ℕ) (F : Finset A) :
    A →ₐ[R] firstAndFinite R A k F :=
  (PiTensorProduct.singleAlgHom (R := R) (A := fun _ : Fin (k + 1) => A) 0).codRestrict _
    (fun a => Algebra.subset_adjoin (Or.inl ⟨a, rfl⟩))

end GlobalTheory.EtC
