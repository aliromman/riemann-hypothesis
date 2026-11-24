import Mathlib
import ReciprocityTheory.GaloisValuations.Global
import ReciprocityTheory.NeutralLocalFields.Duality

open Neutral.B1 ReciprocityTheory.Gal

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
variable (A : ValuationSubring Ω)

example : Subgroup (Ω ≃ₐ[E] Ω) := ReciprocityTheory.Gal.Dec (F := E) A
