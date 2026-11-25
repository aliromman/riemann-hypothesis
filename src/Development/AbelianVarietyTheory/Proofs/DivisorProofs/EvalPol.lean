module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LRowdivLemmas
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

namespace GlobalTheory.CapelliLink

open Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame

abbrev Letter (O : Type) [CommRing O] (N : ℕ) (ι : Type) : Type :=
  (ι → GL (Fin N) O) ⊕ (ι × (Fin N → ℕ))

def evalE (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (lam : ι → ℕ → ℕ)
    (P : ι → (Fin N → ℕ) → Module.End O (NablaT O N lam)) :
    FreeAlgebra O (Letter O N ι) →ₐ[O] Module.End O (NablaT O N lam) :=
  FreeAlgebra.lift O (Sum.elim (grp O N lam) fun p => P p.1 p.2)

def evalPol (O : Type) [CommRing O] (N : ℕ) :
    FreeAlgebra O (Fin N × Fin N) →ₐ[O] Module.End O (MvPolynomial (Fin N × Fin N) O) :=
  FreeAlgebra.lift O fun p => Formalism.GradedWeylDivisibility.rowDivL O p.1 p.2 1

end GlobalTheory.CapelliLink

end
