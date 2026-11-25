module

public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Matrix.Mul
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

namespace GlobalTheory.LeviDesc.Krylov

def krylov {F : Type} [CommRing F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F) (e : Fin r → F) :
    Matrix (Fin r) (Fin r) F :=
  Matrix.of fun i j => Matrix.mulVec (y ^ (j : ℕ)) e i

theorem krylov_apply {F : Type} [CommRing F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F) (e : Fin r → F) (i j : Fin r) :
    krylov y e i j = Matrix.mulVec (y ^ (j : ℕ)) e i := rfl

end GlobalTheory.LeviDesc.Krylov
