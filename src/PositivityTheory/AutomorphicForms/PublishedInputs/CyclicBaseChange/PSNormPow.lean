module

public import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.SConjSpaceC
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.BrData
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValSubLtIff

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Published

private theorem UpperTheory.CBC.NormPowerUnderPlace.normV_under {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K']
    [Algebra K K'] (w : HeightOneSpectrum (𝓞 K')) :
    normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  apply _root_.GlobalTheory.DelEps.WeilRes.normV_eq_pow

theorem UpperTheory.CBC.SNormPow_holds : UpperTheory.CBC.SNormPow := by
  intro K M _ _ _ _ _ w
  exact ⟨_, UpperTheory.CBC.NormPowerUnderPlace.normV_under (K := K) w⟩
