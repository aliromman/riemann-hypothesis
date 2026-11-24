module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsConstMul
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

def FlatDegree : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n)
    (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) [NumberField c.F] (N : LogNorms c.F) [NeZero H.d]
    (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → IsTypeFn H D.p D.q ty → τ (H.rt : E) = H.rt0 →
    IsFlatGen U τ φ FU i → HasNorms U τ φ N →
    N.IsAdelic ∧ N.deg = ((D.p : ℝ) - D.q) / 2 * (GlobalTheory.CM.logOm E χ).re +
      D.q * (2 * Real.log (Real.sqrt H.d) - Real.log (rootDiscr E))

end GlobalTheory.CompanionTheory.Ar.Fl
