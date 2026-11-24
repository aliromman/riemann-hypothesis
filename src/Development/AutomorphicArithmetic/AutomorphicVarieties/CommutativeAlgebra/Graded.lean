module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GrInternal
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

namespace UpperTheory.V.Alg.WPres

variable {O X R : Type} [CommRing O] [AddCommGroup X] [DecidableEq X] [CommRing R] [Algebra O R] (W : WPres O X R)

instance gradedAlgebra : GradedAlgebra W.gr :=
  { (inferInstance : SetLike.GradedMonoid W.gr), (UpperTheory.V.Alg.gr_internal O X R W).chooseDecomposition with }

def originA (h : W.HasOrigin) : W.A →ₐ[O] O := (W.origin h).comp W.A.val


omit [DecidableEq X] in
def quot {R' : Type} [CommRing R'] [Algebra O R'] (p : R →ₐ[O] R') (hp : Function.Surjective p)
    (h : IsHomog O W.wt (RingHom.ker (p.comp W.π))) : WPres O X R' where
  σ := W.σ
  wt := W.wt
  π := p.comp W.π
  surj := hp.comp W.surj
  homog := h

end UpperTheory.V.Alg.WPres
