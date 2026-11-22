module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerTransitive
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

@[expose] public section

alias GlobalTheory.T.eigen_intertwiner_transitive := GlobalTheory.EvNonzero.exists_mem_schA_ev_ne_zero
