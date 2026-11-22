module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ComplexCoordinatesMeasurePreserving
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
public import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement

@[expose] public section

alias GlobalTheory.T.complex_coordinates_measure_preserving := GlobalTheory.ReImVolume.exists_reIm_measurePreserving
