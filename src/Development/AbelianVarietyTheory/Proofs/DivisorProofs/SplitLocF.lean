module

public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
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

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF IsDedekindDomain NumberField
open scoped TensorProduct

namespace GlobalTheory.HeckeSplitGen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


variable (F E) in
def intAEF : AddSubgroup (Af F ⊗[F] E) :=
  AddSubgroup.closure {y | ∃ a : Af F, (∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F) ∧
    ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)}

def splitLocF (σ : E →ₐ[F] E) : Set (AEF F E)ˣ :=
  {x | ∃ e, IsSplitIdemF σ e ∧ (e + cAF σ e) * ((x : AEF F E) - 1) = (x : AEF F E) - 1}


variable (F E) in
def modSetF (N : ℕ) : Set (AEF F E)ˣ :=
  {x | infPartF F E (x : AEF F E) = 1 ∧
    (∃ r ∈ intAEF F E, finPartF F E (x : AEF F E) - 1 = (N : Af F ⊗[F] E) * r) ∧
    finPartF F E ((x⁻¹ : (AEF F E)ˣ) : AEF F E) ∈ intAEF F E}

def grpHF (σ : E →ₐ[F] E) (N : ℕ) : Subgroup (AEF F E)ˣ :=
  Subgroup.closure (Set.range (Units.map (incAF F E).toMonoidHom) ∪ splitLocF σ ∪ modSetF F E N)

end GlobalTheory.HeckeSplitGen

end
