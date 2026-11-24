module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteLengthOfSmulEqZero
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles

@[expose] public section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.TopSteps

theorem reduction_sameSS_of_lattices :
    ∀ {G LL O V : Type} [Group G] [Field LL] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [Algebra O LL] [IsFractionRing O LL] [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
      (ρ : Representation LL G V) (L L' : Lattice (O := O) ρ) (lam : O), Irreducible lam →
      SameSS (modRep (latRep L) lam) (modRep (latRep L') lam) :=
  fun _ L L' _ hlam => lattice_reduction_sameSS hlam L L'

end GlobalTheory.TopSteps
