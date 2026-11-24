module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite
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
import ReciprocityTheory.AnalyticForms.RegularLocalRings.DivSheaf

@[expose] public section

open AlgebraicGeometry CategoryTheory IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.LocM

namespace GlobalTheory.LocM

theorem idlAlong_eq_top_of_notMem_support (X : Scheme.{0}) (I : X.IdealSheafData) (R : Type) [CommRing R]
    [IsLocalRing R] (ξ : Sp R ⟶ X) (h : ξ (closedPoint R) ∉ I.support) : idlAlong I ξ = ⊤ := by
  have e : FinalTheorems.stalkId I (ξ (closedPoint R)) = ⊤ :=
    not_not.1 fun h' => h ((mem_support_iff_stalkId I _).2 h')
  rw [idlAlong, e, Ideal.map_top]

end GlobalTheory.LocM
