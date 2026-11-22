module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonzeroClassBoundedTorsion
public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SelNZero

@[expose] public section

alias GlobalTheory.T.nonzero_class_bounded_torsion := GlobalTheory.Ord2.GwCount.closed_multiplier
