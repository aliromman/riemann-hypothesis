module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.NumberField
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt

def BaseCase : Prop :=
  ∀ (K Ω : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field Ω] [Algebra K Ω] (n : ℕ) (π : CuspSub K n)
    (A : ValuationSubring Ω) (Θ : IsLocalRing.ResidueField A →* ℂ) (v : HeightOneSpectrum (𝓞 K)) e e',
    ResEmb A v e → ResEmb A v e' → ∀ τ τ', π.IsLocComp v τ → π.IsLocComp v τ' →
    ∀ a : Lbl, HasLbl (Θ.comp e.toMonoidHom) τ.ρ a → HasLbl (Θ.comp e'.toMonoidHom) τ'.ρ a

end UpperTheory.Gal.InertialTypesAlt
