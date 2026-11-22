module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UniformBesselConstant
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK

@[expose] public section

alias GlobalTheory.T.uniform_bessel_constant := GlobalTheory.AmpNorm.lintegral_hsNormSq_amp
