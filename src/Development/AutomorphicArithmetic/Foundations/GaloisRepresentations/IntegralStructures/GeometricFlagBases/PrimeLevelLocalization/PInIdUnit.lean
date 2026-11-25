module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.StGood
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

open NumberField IsDedekindDomain
open UpperTheory.Gal.CertificateRingHomMap (Plc)

namespace UpperTheory.Gal.Int.Geo.Pl

private theorem isUnit_algebraMap_adicCompletionIntegers_of_not_mem (E : Type) [Field E] [NumberField E] (w : Plc E) (s : 𝓞 E)
    (hs : s ∉ w.asIdeal) :
    IsUnit (algebraMap (𝓞 E) (HeightOneSpectrum.adicCompletionIntegers E w) s) := by
  rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
  change Valued.v ((algebraMap (𝓞 E) E s : E) : HeightOneSpectrum.adicCompletion E w) = 1
  rw [HeightOneSpectrum.adicCompletion.valued_coe, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_eq_one_iff]
  exact hs

theorem inIdUnit_holds : InIdUnit := by
  intro E _ _ w b c hc y
  obtain ⟨s, hsc, hsw⟩ := hc
  have htop : Ideal.map (algebraMap (𝓞 E) (HeightOneSpectrum.adicCompletionIntegers E w)) c = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hsc) (isUnit_algebraMap_adicCompletionIntegers_of_not_mem E w s hsw)
  unfold InId
  rw [Ideal.map_mul, htop, Ideal.mul_top]

end UpperTheory.Gal.Int.Geo.Pl

end
