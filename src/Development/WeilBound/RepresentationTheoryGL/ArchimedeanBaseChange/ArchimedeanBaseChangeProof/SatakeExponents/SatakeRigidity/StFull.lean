module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.FieldNOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.SplitSatPre
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
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.One

namespace PositivityTheory.Rg.BcB.F.Rig

def UnrAE : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)),
  IsAutRepU π → ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, IsUnramU π w

def InertSatEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ)
  (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π → ∀ w : HeightOneSpectrum (𝓞 E), ¬ IsSplitAt w → IsUnramU π w →
  ∃ (s : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E) (q : ℕ) (α : Fin (n / 2) → ℂˣ),
    (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) ∧ IsUnramInv ϖ s q ∧ HasSatAt π w s ϖ q α

def SplitConj : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)),
  IsAutRepU π → ∀ (D : Pre E n) (w u : HeightOneSpectrum (𝓞 E)), IsSplitAt w → ConjPl w u → IsUnramU π w →
    D.SplitAt π w → D.SplitAt π u → ∀ B B', D.Sat w B → D.Sat u B' → B' = B.map (·⁻¹)

def RFullSat : Prop := UnrAE → InertSatEx → Rig.SplitSatPre → FullSat

def RFullTheta : Prop := UnrAE → InertSatEx → SplitConj → FullTheta

end PositivityTheory.Rg.BcB.F.Rig

end
