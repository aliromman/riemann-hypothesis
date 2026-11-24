module

public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.LandherrStIffLandherr
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCongrIffTraceFormsIsometricCm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LandherrStOfHasseNormSt
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm


open NumberField IsDedekindDomain in
open scoped WithZero in
theorem _root_.GlobalTheory.QNorm.landherr_and_landherrSt :
    _root_.GlobalTheory.Published.Landherr ∧ _root_.GlobalTheory.Published.LandherrSt :=
  ⟨_root_.GlobalTheory.LocalQuad.landherr_of_hasseNormSt _root_.GlobalTheory.QNorm.hasseNormSt,
    _root_.GlobalTheory.LocalQuad.landherrSt_of_hasseNormSt _root_.GlobalTheory.QNorm.hasseNormSt⟩

end GlobalTheory.QNorm
