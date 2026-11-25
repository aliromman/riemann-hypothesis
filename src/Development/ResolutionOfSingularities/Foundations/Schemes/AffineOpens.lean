module

public import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Order.CompletePartialOrder
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

universe u

namespace AlgebraicGeometry.Scheme

theorem exists_isAffineOpen_mem {X : Scheme.{u}} (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U := by
  obtain ⟨U, hU, hxU, -⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens X)
      (show x ∈ (⊤ : X.Opens) from trivial)
  exact ⟨U, hxU, hU⟩

theorem exists_affineOpens_mem {X : Scheme.{u}} (x : X) : ∃ U : X.affineOpens, x ∈ U.1 := by
  have hx : x ∈ (⨆ U : X.affineOpens, (U : X.Opens)) := by
    rw [AlgebraicGeometry.iSup_affineOpens_eq_top X]
    trivial
  obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨U, hU⟩

theorem exists_affineOpens_mem_le {X : Scheme.{u}} {x : X} {U : X.Opens} (hx : x ∈ U) :
    ∃ V : X.affineOpens, x ∈ V.1 ∧ V.1 ≤ U := by
  obtain ⟨V, hV, hxV, hsub⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
  obtain ⟨W, hW, rfl⟩ := hV
  exact ⟨⟨W, hW⟩, hxV, hsub⟩

end AlgebraicGeometry.Scheme
