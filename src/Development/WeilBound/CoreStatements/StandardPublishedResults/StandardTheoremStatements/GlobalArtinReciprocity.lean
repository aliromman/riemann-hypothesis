module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import CompanionTheory.AutomorphicTheory.PlaceSeparation.IsOpenQuotientMapArt0
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

namespace PositivityTheory.Stage1.PM

alias globalArtinReciprocity := _root_.CompanionTheory.FamInh.globalArtin

theorem rayClassFieldSt : GlobalTheory.Published.RayClassFieldSt :=
  GlobalTheory.Published.GlobalArtinReciprocity.rayClassFieldSt CompanionTheory.FamInh.globalArtin

theorem heckeLAdicCharacter : GlobalTheory.Published.HeckeLAdicCharacter :=
  GlobalTheory.Published.GlobalArtinReciprocity.heckeLAdicCharacter CompanionTheory.FamInh.globalArtin

end PositivityTheory.Stage1.PM
