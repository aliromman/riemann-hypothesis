module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
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

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.SecGlue

def chartHom {Y : Scheme.{0}} (V : Y.Opens) {S : Type} [CommRing S] (u : Sp S ⟶ Y)
    (h : u ⁻¹ᵁ V = ⊤) : Γ(Y, V) →+* S :=
  (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom.comp (u.appLE V ⊤ h.ge).hom

def IsCombIn {Y : Scheme.{0}} (V : Y.Opens) {S : Type} [CommRing S] {ι : Type} [Fintype ι]
    (u c : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S) : Prop :=
  ∃ (hu : u ⁻¹ᵁ V = ⊤) (hc : c ⁻¹ᵁ V = ⊤) (hw : ∀ i, w i ⁻¹ᵁ V = ⊤), ∀ x : Γ(Y, V),
    chartHom V c hc x = chartHom V u hu x + ∑ i, a i * (chartHom V (w i) (hw i) x - chartHom V u hu x)

end GlobalTheory.SecGlue
