module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CayleyEndomorphismsUnitary
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.RealPlaceAnalysis.StatementE
public import Formalism.RealPlaceAnalysis.StatementKT

@[expose] public section

alias GlobalTheory.T.cayley_endomorphisms_unitary := GlobalTheory.CapUnitary.isUnitary_of_isE
