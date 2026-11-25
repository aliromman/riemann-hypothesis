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

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL

namespace PositivityTheory.RSHS.LeviInductionForms

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}

def LocMaps (I : Submodule ℂ (Sm E N)) (w : HeightOneSpectrum (𝓞 E)) {X : Type} [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ (GL (Fin N) (w.adicCompletion E)) X) : Type :=
  {F : X →ₗ[ℂ] Sm E N // (∀ v, F v ∈ I) ∧ ∀ g v, F (ρ g v) = finRep E N (locGL E N w g) (F v)}

def LeviMaps {c : ℕ} {n : Fin c → ℕ} (T : Submodule ℂ ((∀ i, GA E (n i)) → ℂ)) (w : HeightOneSpectrum (𝓞 E))
    {X : Type} [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ (∀ i, GL (Fin (n i)) (w.adicCompletion E)) X) : Type :=
  {Φ : X →ₗ[ℂ] ((∀ i, GA E (n i)) → ℂ) // (∀ v, Φ v ∈ T) ∧
    ∀ g v, Φ (ρ g v) = fun m => Φ v fun i => m i * finGL E (n i) (locGL E (n i) w (g i))}

end PositivityTheory.RSHS.LeviInductionForms

end
