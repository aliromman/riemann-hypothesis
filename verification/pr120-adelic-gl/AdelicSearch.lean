module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2DecayOfCountEscape
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralEnormSqLe
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TendstoSetLIntegralDiffCompactCovering
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralNormSqLeToRealLintegralEnormSq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SetLIntegralLeMulFundamentalDomainDiff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CountableSubgroupClosure

public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq

@[expose] public section
open NumberField MeasureTheory Filter Topology
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
variable (K : Type) [Field K] [NumberField K] (n : ℕ)
example : LocallyCompactSpace (AdelicGLn.AdelicGL K n) := inferInstance
example : SecondCountableTopology (AdelicGLn.AdelicGL K n) := inferInstance
example : SigmaCompactSpace (AdelicGLn.AdelicGL K n) := inferInstance
variable (μ : Measure (AdelicGLn.AdelicGL K n)) [μ.IsHaarMeasure]
example : SigmaFinite μ := inferInstance
example (s : Set (AdelicGLn.AdelicGL K n)) : SFinite (μ.restrict s) := inferInstance
