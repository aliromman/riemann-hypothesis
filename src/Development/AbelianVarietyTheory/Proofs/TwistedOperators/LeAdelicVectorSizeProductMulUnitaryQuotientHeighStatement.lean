module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VsizeNonneg
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeAdelicVectorSizeProductMulUnitaryQuotientHeigh
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix

theorem _root_.GlobalTheory.T.le_adelicVectorSizeProduct_mul_unitaryQuotientHeight_pow : ∀ (D : D7) (V : HSp D), ∃ (c : ℝ) (N : ℕ), 0 < c ∧ ∀ (g : GA D V) (ξ : Fin V.rank → D.host.E), ξ ≠ 0 → c ≤ GlobalTheory.HtOrth.vsize (GlobalTheory.HtOrth.seen V g ξ) * GlobalTheory.Grow.quotHeight V g ^ N := by
  first | exact @GlobalTheory.SeenSize.le_vsize_mul_quotHeight
