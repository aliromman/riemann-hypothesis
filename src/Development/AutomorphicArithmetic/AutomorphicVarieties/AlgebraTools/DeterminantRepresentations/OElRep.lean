module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.FlagRel
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

open Polynomial Matrix UpperTheory.V UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.oElRep :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (r : F.G₀ →* GL (Fin n) R) (v : F.Vl) (ψ : Fin n → F.Gv v →* Rˣ), HasFlag (r.comp (F.φ v)) ψ →
    ∀ g, GDet.repAlg (mat r) R (F.oEl v ψ g) = 0 := by
  intro l _ F O _ _ R _ _ n r v ψ h g
  rw [← (UpperTheory.V.AlgebraTools.Det.flagRel _ _ h).2 g, GFrame.oEl, map_list_prod, List.map_ofFn]
  congr 2
  funext i
  simp [GDet.repAlg, mat, MonoidAlgebra.lift_single]
