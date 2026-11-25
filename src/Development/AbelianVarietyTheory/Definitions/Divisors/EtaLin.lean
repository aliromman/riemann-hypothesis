module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Rosati
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

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

structure PreEta (b : Base D R) (N : ℕ) (s : S ⟶ Sp R) extends Pre b s where
  eta : D.La → (𝟙_ (Over S) ⟶ A)
  eta_add : ∀ x y, eta (x + y) = eta x * eta y
  eta_lin : ∀ (c : D.O) x, eta (c • x) = eta x ≫ act.act c
  eta_ker : ∀ x, eta (N • x) = 1

def PreEta.GeomAt {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} (o : PreEta b N s) (k : Type) [Field k] (x : Sp k ⟶ S) : Prop :=
  ∃ I : TateIsoO D k (Over.mk x ⟶ o.A) (fun c g => g ≫ o.act.act c)
      (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)),
    ∀ y, toUnit _ ≫ o.eta y = I.ev N y

end GlobalTheory.UPel.HT
