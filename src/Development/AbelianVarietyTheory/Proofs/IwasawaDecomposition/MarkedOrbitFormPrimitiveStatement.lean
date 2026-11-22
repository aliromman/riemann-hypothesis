module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkedOrbitFormPrimitive
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfIsOrbFormConst

@[expose] public section

alias GlobalTheory.T.markedOrbit_form_primitive := GlobalTheory.PolFan.OrbMark.eq_one_of_smul_eq_of_orbFun_evalZ_eq_one
