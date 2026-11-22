module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankIffNonzeroMinor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmAOneApply

@[expose] public section

alias GlobalTheory.T.full_rank_iff_nonzero_minor := GlobalTheory.RankFibreKer.rank_eq_iff_exists_minor_ne_zero
