module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsIntZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.LeftInv
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ReadSplit
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.IsTransl
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.IsSliceMap

@[expose] public section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.CtS.NuVal

theorem ord_eq_ordL_unit {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (x : (w.adicCompletion E)ˣ) : GlobalTheory.SmGL.ord (w.adicCompletion E) x = ordL (x : w.adicCompletion E) := by
  have h : Valued.v (x : w.adicCompletion E) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
  rw [GlobalTheory.SmGL.SphCompletion.ord_completion]
  unfold ordL
  rw [dite_eq_right h]
  congr 1
  conv_lhs => rw [← WithZero.coe_unzero h]
  first | rfl

theorem unrChar_twist : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (c : ℂˣ) (i j : ℕ) (m : GLw a w × GLw b w), ordL m.1.val.det = (i : ℤ) → ordL m.2.val.det = (j : ℤ) → (GlobalTheory.SmGL.unrChar (w.adicCompletion E) c ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) : ℂ) = (c : ℂ) ^ (i * b + j * a) := by
  intro E _ _ _ a b w c i j m h1 h2
  have hneg : GlobalTheory.SmGL.unrChar (w.adicCompletion E) c (-1) = 1 := by
    rw [GlobalTheory.SmGL.unrChar_apply, GlobalTheory.SmGL.ord_eq_zero (by simp), zpow_zero]
  have hd1 : GlobalTheory.SmGL.unrChar (w.adicCompletion E) c (GeneralLinearGroup.det m.1) = c ^ i := by
    rw [GlobalTheory.SmGL.unrChar_apply, ord_eq_ordL_unit]
    erw [h1]
    simp
  have hd2 : GlobalTheory.SmGL.unrChar (w.adicCompletion E) c (GeneralLinearGroup.det m.2) = c ^ j := by
    rw [GlobalTheory.SmGL.unrChar_apply, ord_eq_ordL_unit]
    erw [h2]
    simp
  rw [map_mul, map_mul, map_pow, map_pow, map_pow, hneg, hd1, hd2, one_pow, one_mul, ← pow_mul, ← pow_mul,
    ← pow_add]
  simp

end GlobalTheory.CompanionTheory.CtS.NuVal
