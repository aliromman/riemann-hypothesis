module
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnipotentLatticeMembership
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsFin
open Formalism.BasicNotions Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnipotentLatticeMembership
open Formalism.L2.SG.Pf.AllRowsFin

example (D : D7) : finiteLevelGroupFintype D = finiteReductionGroup D := rfl

example (D : D7) : finiteLevelGroupFintype D = Fintype.ofFinite (G0g D.nd) :=
  Subsingleton.elim _ _
