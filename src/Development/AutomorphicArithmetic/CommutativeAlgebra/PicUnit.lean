module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC TensorProduct

namespace UpperTheory.PicD

theorem unitSec_mul {U : Scheme.{0}} (u v : (Γ(U, ⊤))ˣ) : unitSec (u * v) = unitSec u + unitSec v := by
  unfold unitSec ofRings.sec
  exact map_add (ModuleCat.Hom.hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op U)))
    (⟨Additive.ofMul u⟩ : ULift.{1, 0} (Additive (Γ(U, ⊤))ˣ)) ⟨Additive.ofMul v⟩

theorem unitSec_one {U : Scheme.{0}} : unitSec (1 : (Γ(U, ⊤))ˣ) = 0 := by
  unfold unitSec ofRings.sec
  exact map_zero (ModuleCat.Hom.hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op U)))

theorem unitSec_res {V U : Scheme.{0}} (g : V ⟶ U) (u : (Γ(U, ⊤))ˣ) :
    Sec.res g (unitSec u) = unitSec (Units.map g.appTop.hom.toMonoidHom u) := by
  unfold unitSec ofRings.sec
  have h := congrArg (fun f => (ModuleCat.Hom.hom f)
    (⟨Additive.ofMul u⟩ : ULift.{1, 0} (Additive (Γ(U, ⊤))ˣ)))
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).naturality g.op)
  exact h.symm

end UpperTheory.PicD
