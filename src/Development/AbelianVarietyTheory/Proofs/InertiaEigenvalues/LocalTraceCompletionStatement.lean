module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalTraceCompletion
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands

@[expose] public section

alias GlobalTheory.T.local_trace_completion := GlobalTheory.LocLanglands.TraceCompl.exists_trace_extension
