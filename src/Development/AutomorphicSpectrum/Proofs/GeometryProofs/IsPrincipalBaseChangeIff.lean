module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
public import Development.WeilBound.CoreStatements.AmpleLineBundles.IsPrincipalIffOfBaseChange
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem isPrincipal_iff_of_sabMap_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L L' : Type) [Field L] [Field L'] (e : L →+* L') (t : SAB H (Sp L)) (t' : SAB H (Sp L')) (_ : SABMap t' t (spMap e)), IsPrincipal t' ↔ IsPrincipal t := by
  exact @CoverDenseAlt.isPrincipal_iff_of_base_change

end GlobalTheory.CompanionTheory.Ar
