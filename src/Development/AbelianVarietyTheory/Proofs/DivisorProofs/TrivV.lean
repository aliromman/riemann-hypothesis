module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
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
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.EtC

def trivV (N : ℕ) (E : Spc) : E ⟶ ofCat (glCat N) where
  app n :=
    { app := fun U => TypeCat.ofHom fun _ =>
        (show Fin (n.unop.len + 1) ⥤ (glCat N).obj (Scheme.Γ.obj U) from
          (CategoryTheory.Functor.const _).obj (SingleObj.star (GL (Fin N) (Scheme.Γ.obj U))))
      naturality := fun U U' f => by
        ext x
        exact CategoryTheory.Functor.hext (fun _ => rfl)
          (fun _ _ _ => heq_of_eq (map_one (Matrix.GeneralLinearGroup.map _)).symm) }
  naturality n m f := by
    ext U x
    exact CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => heq_of_eq rfl)

end GlobalTheory.EtC

end
