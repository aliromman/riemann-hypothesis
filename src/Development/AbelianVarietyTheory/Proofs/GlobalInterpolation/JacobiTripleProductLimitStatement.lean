module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JacobiTripleProductLimit
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MultipliableTpFactor

@[expose] public section

alias GlobalTheory.T.jacobi_triple_product_limit := GlobalTheory.JacobiTriple.tendsto_finCoeff_sum_jacobiTheta₂
