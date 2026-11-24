module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import GroundTheory.GlobalFields.Adele.Approximation
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

noncomputable section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.RedCov.Simple

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def boxF (ρ : ℝ) : Set (AF F) :=
  {a | (∀ w : InfinitePlace F, ‖a.1 w‖ ≤ ρ) ∧ a.2 ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F}

def boxE (ρ : ℝ) : Set (AF F ⊗[F] E) :=
  {x | ∀ k, (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).repr x k ∈ boxF F ρ}

end GlobalTheory.CompanionTheory.RedCov.Simple

end
