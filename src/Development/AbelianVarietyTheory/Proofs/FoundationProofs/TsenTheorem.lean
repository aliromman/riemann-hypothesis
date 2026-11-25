module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.C1FiniteExtensionLang
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TsenLangRatFunc
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

open GlobalTheory.NeedB Polynomial

namespace GlobalTheory.NeedB

theorem tsen : Tsen := by
  intro k K _ _ _ _ _
  exact _root_.GlobalTheory.is_c1_of_finite_of_tsen_lang_systems (RatFunc k) K (_root_.GlobalTheory.tsenLang_ratFunc k)

end GlobalTheory.NeedB
