module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DegenerationDataCoordsNeZeroLatticesIsomorphic
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

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.PolNormal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem polAt_generic_pull {S T : Type} [CommRing S] [IsDomain S] [CommRing T] [IsDomain T] (i : S →+* T)
    (hi : Function.Injective i) {t : SAB H (Sp S)} {t' : SAB H (Sp T)} (m : SABMap t' t (spMap i))
    (hg : GlobalTheory.LN.PolAt t (Out.jK S)) : GlobalTheory.LN.PolAt t' (Out.jK T) := by
  let ι : FractionRing S →+* FractionRing T :=
    IsLocalization.map (FractionRing T) i (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective i hi)
  refine GlobalTheory.DatUniq.polAt_pull m hg (Out.jK T) (spMap ι) ?_
  simp only [spMap, Out.jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact IsLocalization.map_comp _

end GlobalTheory.PolNormal

namespace GlobalTheory.PolNormal

end GlobalTheory.PolNormal

namespace GlobalTheory.PolNormal
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

end GlobalTheory.PolNormal

namespace GlobalTheory.PolNormal

end GlobalTheory.PolNormal
