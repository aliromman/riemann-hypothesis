module

public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneCharpolyTwistSpecial
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RestrictsSelf
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.RoadU.CharSupport

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem charPol_seg {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
    {rc : IrrGL (k := w.adicCompletion E) → WD h} (H : UpperTheory.Zero.LLC.LawsT a ha rc) (Δ : Segment (w.adicCompletion E))
    (σ : Weil h) :
    (((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) Δ.len)).charPol σ
      = (Δ.ms.map fun y => (rc y).charPol σ).prod := by
  rw [(GlobalTheory.WeilDeligne.charPol_lpTw_lpChar_lpSp E Ω A w h (rc Δ.first)).2 Δ.len σ, Segment.ms, Multiset.map_map]
  have h1 : ∀ j : Fin Δ.len, (rc (Δ.term j)).charPol σ = ((rc Δ.first).lpTw ((j : ℕ) : ℝ)).charPol σ := by
    intro j
    rw [Segment.term, show (((j : ℕ) : ℂ)) = ((((j : ℕ) : ℝ)) : ℂ) by push_cast; rfl, H.nu]
  change _ = ∏ j : Fin Δ.len, (fun y => (rc y).charPol σ) (Δ.term j)
  simp only [h1]
  rw [Fin.prod_univ_eq_prod_range (fun j => ((rc Δ.first).lpTw (j : ℝ)).charPol σ) Δ.len]
  rfl

end GlobalTheory.RoadU.CharSupport

end
