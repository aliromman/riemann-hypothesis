module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZetaValueIdeals
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedTransport
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

namespace GlobalTheory.Mem.LiteralAutomorphy

def JoinOut : Prop :=
  GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator ∧ GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Transport ∧ GlobalTheory.ToricTransport.TwistedTransport ∧
    GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.ZetaDenominators ∧ GlobalTheory.SqTop.Refl

end GlobalTheory.Mem.LiteralAutomorphy

namespace GlobalTheory.Fc.S0


end GlobalTheory.Fc.S0
