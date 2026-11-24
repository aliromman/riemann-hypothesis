module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.TorusScalar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BernsteinZelevinskyFinitenessHolds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedNeBotOfIsSubquotient
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ApplyMemTwKerOfNormalizer
public import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.GlnMixed
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MoyPrasadJacquetIso
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TotallyDisjointProductIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GrothendieckRingPolynomial
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.TotallyDisjointProductIrreducibleOfPolynomialRin
import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.GrothendieckRingPolynomialOfSeg
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.SegmentRepresentation
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

namespace UpperTheory.Gal.TypesAndIwahori

theorem loc_holds : Loc := by
  have geo := UpperTheory.Lit.Mix.geometricLemma
  have bz := GlobalTheory.bernsteinZelevinskyFiniteness_holds
  have zel := UpperTheory.Lit.Mix.polynomialRing
  have seg := PositivityTheory.RgGu.segmentRepresentation
  exact
    { bz := bz
      geo := geo
      zel := zel
      disj := _root_.GlobalTheory.CompanionTheory.Hypotheses₂.totallyDisjointProductIrreducible_of_parts geo seg
        (PositivityTheory.Groth.grothendieckRingPolynomial_of_seg seg)
      mp := GlobalTheory.CompanionTheory.MoyPrasadTop.moyPrasadJacquetIso
      dzi := GlobalTheory.DepthZeroPass.depthZeroInduction geo bz zel
      dzj := GlobalTheory.DepthZeroJac.depthZeroJacquetInjective }

end UpperTheory.Gal.TypesAndIwahori
