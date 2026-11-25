module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
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

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.F.F5.Bo

def LocUniq : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (V : Submodule ℂ (Sm E N)),
  IsDiscrete V → ∀ (w : HeightOneSpectrum (𝓞 E)) (σ σ' : SmIrr (GL (Fin N) (w.adicCompletion E))),
    IsLocCompGL V w σ → IsLocCompGL V w σ' →
      GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred = GlobalTheory.LocGL.IrrGL.of σ'.ρ σ'.smooth σ'.irred

def LocIso : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (V V' : Submodule ℂ (Sm E N)),
  SpectralAccumulation.IsoV V V' → ∀ (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin N) (w.adicCompletion E))),
    IsLocCompGL V w σ → IsLocCompGL V' w σ

def FinIso : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (K : Subgroup (GL (Fin N) (Af E)))
  (W : Submodule ℂ (Kinf E N → ℂ)) (m : (E →+* ℂ) → Multiset ℂ), IsOpen (K : Set (GL (Fin N) (Af E))) →
  FiniteDimensional ℂ W → ∃ V₀ : Finset (Submodule ℂ (Sm E N)), (∀ V ∈ V₀, IsDiscrete V) ∧
    ∀ V : Submodule ℂ (Sm E N), IsDiscrete V → SpectralAccumulation.HasType K W V → (∀ τ, HasInfCharGL V τ (m τ)) →
      ∃ V' ∈ V₀, SpectralAccumulation.IsoV V V'

end PositivityTheory.Rg.BcB.F.F5.Bo

end
