module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilStandard.SiegelWeilStd
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.MemClosureOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.ProjEx
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0013
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0025
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0009
public import Mathlib
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0015
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0020
public import Development.WeilBound.ThetaLifts.LatticeBasics.LocUnrSplit
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0025
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0026
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0007
public import Development.WeilBound.ThetaLifts.LatticeBasics.OrthAn
public import Development.WeilBound.ThetaLifts.LatticeBasics.OffOpen
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0010
public import Development.WeilBound.ThetaLifts.TowerModels.TowerCodimensionTwo
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairExistence.WeilEx
public import Development.WeilBound.ThetaLifts.Reductions.LieScalar2
public import Development.WeilBound.ThetaLifts.Reductions.LocalLift
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0029
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0011
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0076
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0062
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0097
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0048
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPGDecomp
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPGBumpAny
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPGDatum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0085
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0084
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPGReadLift

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPGTop
section
set_option synthInstance.maxHeartbeats 200000

section
namespace UpperTheory.TP
theorem tLift_of_tools_k (T : _root_.UpperTheory.TP.Tools_k) (hH : _root_.GlobalTheory.ThK.Dbl.HgtEx_k) : _root_.UpperTheory.TP.TLift_k :=
  _root_.UpperTheory.TP.tLift_of_k T hH brEx (_root_.UpperTheory.TP.hgtFst_k T) (_root_.UpperTheory.TP.realPair_k T)
    (_root_.UpperTheory.TP.nonVan_k T (_root_.UpperTheory.TP.rallis_k T) (_root_.UpperTheory.TP.decomp_k T) (_root_.UpperTheory.TP.bumpAny_k T) (_root_.UpperTheory.TP.datum_k T) (_root_.UpperTheory.TP.tail_k T) absNe (_root_.UpperTheory.TP.schurStep_k T)) (_root_.UpperTheory.TP.liftAut_k T) projEx
    (_root_.UpperTheory.TP.readLift_k T (_root_.UpperTheory.TP.liftAut_k T) absIso)
end UpperTheory.TP
end
end

