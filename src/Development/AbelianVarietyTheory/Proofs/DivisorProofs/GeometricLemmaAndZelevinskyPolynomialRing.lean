module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BzfinHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricLemmaFiltrationUnconditional
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GrothendieckRingPolynomialOutright
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SegmentRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GeometricLemmaOfFiltration
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZelevinskyGrothendieckPolynomialRingOfSegments
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

namespace GlobalTheory

theorem geometricLemma_and_zelevinskyPolynomialRing :
    GlobalTheory.Published.GeometricLemma ∧ GlobalTheory.Published.ZelevinskyPolynomialRing :=
  ⟨GlobalTheory.geometricLemma_of_filtration _root_.GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
               _root_.CompanionTheory.Geo.geometricLemmaFiltration,
    GlobalTheory.zelevinskyPolynomialRing_of_parts _root_.GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
      _root_.CompanionTheory.RgGu.segmentRepresentation GlobalTheory.grothendieckRingPolynomial_outright⟩

end GlobalTheory
