module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.StrictJoin
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleParabolicInduction
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryLevelSubgroupProperties
import GroundTheory.LocalFields.PadicLogSeries
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

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical



namespace PositivityTheory.Rg.BcB.F.FX.Bo

theorem AdmProd_holds : AdmProd := by
  intro E _ _ _ n P w K hKo hKle
  have hadm := GlobalTheory.CompanionTheory.ProdAdm.isAdmissible_multiProd_smIrr (w.adicCompletion E) P.N P.h (fun i => P.σ i w)
  have hKc : IsCompact (K : Set (GLw n w)) :=
    (GlobalTheory.CompanionTheory.IwLevels.isCompact_KGL w n).of_isClosed_subset (K.isClosed_of_isOpen hKo) hKle
  exact hadm.2 K hKo hKc

end PositivityTheory.Rg.BcB.F.FX.Bo

end
