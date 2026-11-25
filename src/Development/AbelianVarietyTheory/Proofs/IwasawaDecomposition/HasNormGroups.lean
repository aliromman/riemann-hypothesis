module

public import ReciprocityTheory.NeutralLocalFields.Reciprocity
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
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

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne Neutral.B1

namespace GlobalTheory.LocDict

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

abbrev Kbar (w : HeightOneSpectrum (𝓞 E)) : Type := AlgebraicClosure (w.adicCompletion E)

abbrev GalLoc (w : HeightOneSpectrum (𝓞 E)) : Type := Kbar w ≃ₐ[w.adicCompletion E] Kbar w

def IsLocEmb (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (ι : Ω →ₐ[E] Kbar w) : Prop :=
  ∀ z, z ∈ A ↔ IsIntegral (w.adicCompletionIntegers E) (ι z)

def Lifts {w : HeightOneSpectrum (𝓞 E)} (ι : Ω →ₐ[E] Kbar w) (g : GalLoc w) (σ : G E Ω) : Prop :=
  ∀ z, g (ι z) = ι (σ z)

theorem Lifts.eq {w : HeightOneSpectrum (𝓞 E)} {ι : Ω →ₐ[E] Kbar w} {g : GalLoc w} {σ σ' : G E Ω}
    (H : Lifts ι g σ) (H' : Lifts ι g σ') : σ = σ' :=
  AlgEquiv.ext fun z => ι.toRingHom.injective ((H z).symm.trans (H' z))

variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

def HasNormGroups (h : IsPlaceOver A w) (ι : Ω →ₐ[E] Kbar w) (a : Weil h →* (w.adicCompletion E)ˣ) : Prop :=
  ∀ L : IntermediateField (w.adicCompletion E) (Kbar w), IsFiniteAbelian (w.adicCompletion E) L →
    ∀ (σ : Weil h) (g : GalLoc w), Lifts ι g σ → ((∀ z ∈ L, g z = z) ↔ a σ ∈ normGroup (w.adicCompletion E) L)

end GlobalTheory.LocDict

end
