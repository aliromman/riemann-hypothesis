module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
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
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

namespace PositivityTheory.RSHS.LocalComponentTwist

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}

theorem isLocComp_twist {a : ℕ} (π : CuspSub E a) (χ : HChar E) {w : HeightOneSpectrum (𝓞 E)}
    {σ : SmIrr (GL (Fin a) (w.adicCompletion E))} (hσ : π.IsLocComp w σ) :
    (π.twist χ).IsLocComp w (σ.twist (CuspSub.locDet a χ w) (CuspSub.isOpen_ker_locDet χ w)) :=
  CuspSub.IsLocComp.twist hσ χ

end PositivityTheory.RSHS.LocalComponentTwist

end
