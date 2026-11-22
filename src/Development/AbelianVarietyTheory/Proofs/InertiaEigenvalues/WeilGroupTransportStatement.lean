module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilGroupTransport
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands

@[expose] public section

alias GlobalTheory.T.weil_group_transport := GlobalTheory.LocLanglands.exists_isLocalExt_transport
