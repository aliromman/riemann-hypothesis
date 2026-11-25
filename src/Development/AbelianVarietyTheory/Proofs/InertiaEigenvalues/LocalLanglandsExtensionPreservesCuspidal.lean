module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
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

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published

noncomputable section

namespace GlobalTheory.LocLanglands.CuspExt

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem charPol_lpZero (σ : Weil h) : (WD.lpZero (h := h)).charPol σ = 1 := by
  rw [WD.lpZero, WD.charPol_mk]
  exact Polynomial.eq_one_of_monic_natDegree_zero (LinearMap.charpoly_monic _)
    (by rw [LinearMap.charpoly_natDegree]; simp)

theorem charPol_sumList (l : List (WD h)) (σ : Weil h) :
    (GlobalTheory.LocLanglands.sumList l).charPol σ = (l.map fun y => y.charPol σ).prod := by
  induction l with
  | nil => simp [GlobalTheory.LocLanglands.sumList, charPol_lpZero]
  | cons b l ih =>
    have : GlobalTheory.LocLanglands.sumList (b :: l) =
        WD.lpSum b (GlobalTheory.LocLanglands.sumList l) := rfl
    rw [this, WD.charPol_lpSum, ih, List.map_cons, List.prod_cons]

variable {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
  {e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ} {r : IrrGL (k := w.adicCompletion E) → WD h}

end GlobalTheory.LocLanglands.CuspExt

namespace GlobalTheory.LocLanglands

end GlobalTheory.LocLanglands

end
