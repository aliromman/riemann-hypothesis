module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdmissibleLatticeBasisExists
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll

@[expose] public section

alias GlobalTheory.T.admissible_lattice_basis_exists := GlobalTheory.HomLocBasis.exists_nnBasis
