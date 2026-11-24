module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLeFinrankLa
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

@[expose] public section

noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

def Obj.toSieg {b : Base D R} {N : ℕ} {t : S ⟶ Sp R} (o : Obj b N t) {h M : ℕ} {B : Type} [CommRing B] {ζ : B}
    {t₁ : S ⟶ Sp B} {lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ o.A)} (hl : IsSympLev o.P h M ζ t₁ lev) :
    SiegPre h M ζ t₁ where
  A := o.A
  ab := o.ab
  P := o.P
  isLB := o.isLB
  rig₁ := o.rig₁
  rig₂ := o.rig₂
  symm := o.symm
  lev := lev
  lev_add := hl.1
  lev_tors := hl.2.1
  geom := hl.2.2

theorem Obj.toSieg_ample {b : Base D R} {N : ℕ} {t : S ⟶ Sp R} (o : Obj b N t) {h M : ℕ} {B : Type} [CommRing B]
    {ζ : B} {t₁ : S ⟶ Sp B} {lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ o.A)} (hl : IsSympLev o.P h M ζ t₁ lev) :
    Out.RelAmple (o.toSieg hl).A (o.toSieg hl).diag := o.ample

end GlobalTheory.UPel.HT
