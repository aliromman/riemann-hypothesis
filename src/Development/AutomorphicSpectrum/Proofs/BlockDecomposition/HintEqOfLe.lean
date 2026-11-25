module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsumOutOfLe
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
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfNonNil

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.HintSmaller

theorem hint_eq_of_le : ∀ {H : Type} [Group H] (K S : Subgroup H) (u : H → ℂ), S ≤ K → S ≤ rStab u →
    S.relIndex K ≠ 0 → (Function.support fun q : H ⧸ S => u q.out).Finite →
    hint K u = ((S.relIndex K : ℂ))⁻¹ * ∑ᶠ q : H ⧸ S, u q.out := by
  intro H _ K S u hSK hSu hfin _
  exact GlobalTheory.CompanionTheory.HintLevel.hint_eq_level H K S u hSK hSu hfin

end GlobalTheory.CompanionTheory.HintSmaller
