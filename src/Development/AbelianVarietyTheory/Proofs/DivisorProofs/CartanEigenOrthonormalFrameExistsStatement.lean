module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanEigenOrthonormalFrameExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique

@[expose] public section

alias GlobalTheory.T.cartanEigen_orthonormalFrame_exists := GlobalTheory.RealLift.frameEx_holds
