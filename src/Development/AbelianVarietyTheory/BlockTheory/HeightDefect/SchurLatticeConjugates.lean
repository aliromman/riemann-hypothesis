module

public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

open NumberField IsDedekindDomain

namespace GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

noncomputable def ord_vw {K : Type} [Field K] [NumberField K]
    (la : HeightOneSpectrum (𝓞 K)) (I : Ideal (𝓞 K)) : ℕ :=
  multiplicity la.asIdeal I

noncomputable def conjDifferent {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (σ : E →+* K) : Ideal (𝓞 K) :=
  (differentIdeal ℤ (𝓞 E)).map (RingOfIntegers.mapRingHom σ)

theorem conjDifferent_ne_bot {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (σ : E →+* K) : conjDifferent σ ≠ ⊥ := by
  have hinj : Function.Injective (RingOfIntegers.mapRingHom σ) := by
    intro x y h
    apply RingOfIntegers.ext
    apply σ.injective
    simpa using congrArg (fun z : 𝓞 K => (z : K)) h
  unfold conjDifferent
  rw [Ne, Ideal.map_eq_bot_iff_of_injective hinj]
  exact differentIdeal_ne_bot

noncomputable def lrd (E : Type) [Field E] [NumberField E] : ℝ :=
  Real.log (rootDiscr E)

end GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects
