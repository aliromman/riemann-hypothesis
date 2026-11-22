module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalNormResidueSignMul
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

@[expose] public section

alias GlobalTheory.T.localNormResidueSign_mul := GlobalTheory.KSp.sgn_mul_of_isQuad
