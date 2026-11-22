module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GluingLawHolds
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChosenSeries

@[expose] public section

alias GlobalTheory.T.gluing_law_holds := GlobalTheory.Chain.RealIt.GlueProof.glueLaw
