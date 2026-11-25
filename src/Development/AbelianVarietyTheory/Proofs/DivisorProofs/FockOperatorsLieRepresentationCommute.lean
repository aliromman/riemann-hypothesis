module

public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActDualPairCommutingLieActions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockQuadraticActionMapLieBracket
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
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Formalism.SharpRestriction.Divisibility.SchurIrreducible

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.FockAlg


open MvPolynomial in
theorem _root_.GlobalTheory.FockAlg.fock_lie_and_commute : ∀ (p q r s : ℕ),
    (∀ Y Z, _root_.Formalism.BasicNotions.TH.omAct p q r s (Y * Z - Z * Y) =
      _root_.Formalism.BasicNotions.TH.omAct p q r s Y * _root_.Formalism.BasicNotions.TH.omAct p q r s Z - _root_.Formalism.BasicNotions.TH.omAct p q r s Z * _root_.Formalism.BasicNotions.TH.omAct p q r s Y) ∧
    _root_.Formalism.BasicNotions.TH.IsLieAct (_root_.Formalism.BasicNotions.TH.fockAct1 p q r s) ∧ _root_.Formalism.BasicNotions.TH.IsLieAct (_root_.Formalism.BasicNotions.TH.fockAct2 p q r s) ∧
    ∀ Y Z, _root_.Formalism.BasicNotions.TH.fockAct1 p q r s Y * _root_.Formalism.BasicNotions.TH.fockAct2 p q r s Z = _root_.Formalism.BasicNotions.TH.fockAct2 p q r s Z * _root_.Formalism.BasicNotions.TH.fockAct1 p q r s Y :=
  fun p q r s => ⟨_root_.GlobalTheory.FockLie.omAct_lie p q r s,
    _root_.GlobalTheory.FockPair.pair_lie_commute p q r s⟩

end GlobalTheory.FockAlg
