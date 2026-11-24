module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb
public import GroundTheory.AutomorphicForms.SatakeNormalized
public import GroundTheory.AutomorphicForms.WhittakerGroups
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

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic
open scoped ValuativeRel

namespace UpperTheory.V.Af.Smo

def SphDict : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E)),
    GLnLocal.integralGL (w.adicCompletion E) n = GlobalTheory.LFun.KGL w (n := n) ∧
    Formalism.UG.IsUnifV E w (GLnLocal.uniformizer (w.adicCompletion E) : w.adicCompletion E) ∧
    (∀ r ≤ n, Spherical.sqrtQ (w.adicCompletion E) ^ (r * (n - r)) =
      (Formalism.UG.qV E w : ℂ) ^ (((r : ℂ) * ((n : ℂ) - r)) / 2)) ∧
    ∀ u ∈ Iwasawa.unipotent (w.adicCompletion E) n, IsY 0 u.val ∧
      ∀ ψ : AddChar (w.adicCompletion E) ℂ, Whittaker.psiN ψ u = ψ (supN u.val)

def TjSet : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E)), ∀ r ≤ n,
    Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) (GLnLocal.uniformizer (w.adicCompletion E) : w.adicCompletion E) r =
      (Spherical.minusculeSet (w.adicCompletion E) n r).indicator fun _ => (1 : ℂ)

end UpperTheory.V.Af.Smo
