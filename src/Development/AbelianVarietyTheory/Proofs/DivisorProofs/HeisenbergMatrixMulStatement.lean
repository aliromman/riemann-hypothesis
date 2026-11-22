module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergMatrixMul
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatMulVec

@[expose] public section

alias GlobalTheory.T.heisenberg_matrix_mul := GlobalTheory.UnipMass.nmat_mul_nmat
