module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalityPreservedInClosure
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector

@[expose] public section

alias GlobalTheory.T.cuspidality_preserved_in_closure := GlobalTheory.HolDict.ZClosed.zcusp_of_mem_closure
