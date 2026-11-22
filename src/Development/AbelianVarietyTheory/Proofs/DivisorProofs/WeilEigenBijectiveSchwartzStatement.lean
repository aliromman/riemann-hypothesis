module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenBijectiveSchwartz
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

@[expose] public section

alias GlobalTheory.T.weil_eigen_bijective_schwartz := GlobalTheory.ModelTr.exists_isWeil_trans_of_bijOn
