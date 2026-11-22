module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerComparison
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
public import Development.AbelianVarietyTheory.Definitions.Divisors.P22

@[expose] public section

alias GlobalTheory.T.kodaira_spencer_comparison := GlobalTheory.LogPole.exists_ksCompare
