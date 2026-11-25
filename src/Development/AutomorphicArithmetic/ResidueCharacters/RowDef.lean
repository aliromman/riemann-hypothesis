module

public import Formalism.SharpRestriction.LevelLetterCocycles.SmallTwists.RowSmall
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
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

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace UpperTheory.N

def costC {D : D7} (L : SizeData₂ D) (A B : ℝ) (l : ℕ) : ℝ :=
  A * D.R.f * D.R.m * RowSmall.hB L * (RowSmall.sl D l : ℝ) +
    B * (D.R.f : ℝ) ^ 2 * (D.R.t : ℝ) ^ 2 * D.R.nV * RowSmall.abelian₂ L l

def RowAt {D : D7} (L : SizeData₂ D) (ρ : FamilyRepresentationConstants.RhoFam D) (A B : ℝ) : Prop :=
  ∀ k, TwistedPlaces.TwLoc D k → D.nd.l k ∈ D.host.small → D.nd.l k ≠ 2 → ∀ π ∈ D.nd.Zgood k, Bd ρ k π (costC L A B (D.nd.l k))

end UpperTheory.N

end
