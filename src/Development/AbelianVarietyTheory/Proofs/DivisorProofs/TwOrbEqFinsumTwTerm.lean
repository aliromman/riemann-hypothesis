module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
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

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

noncomputable section

namespace GlobalTheory.EulerAbs

variable {G : Type} [Group G] [TopologicalSpace G]

def twTerm (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) (y : G) : ℂ :=
  (((twCent θ δ ⊓ K.map (MulAut.conj y).toMonoidHom).relIndex (cptPart (twCent θ δ)) : ℕ) : ℂ) *
    avg fun k : K => f ((y * k)⁻¹ * δ * θ (y * k))

theorem twOrb_eq_finsum_twTerm (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) :
    twOrb θ K δ f = ∑ᶠ q : DoubleCoset.Quotient (twCent θ δ : Set G) (K : Set G), twTerm θ K δ f (Quotient.out q) :=
  rfl

end GlobalTheory.EulerAbs
