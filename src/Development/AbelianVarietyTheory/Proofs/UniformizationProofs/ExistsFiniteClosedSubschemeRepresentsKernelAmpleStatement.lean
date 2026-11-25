module

public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFiniteClosedSubschemeRepresentsKernelAmple
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

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_finite_closed_subscheme_represents_kernel_ample : GlobalFnsSt → ∀ (V : Type) [CommRing V] (B : Over (Sp V)) [GrpObj B], IsAbelianScheme B → ∀ L : LB B.left, L.IsLB → RelAmple B L → ∃ (H : Over (Sp V)) (j : H ⟶ B), IsClosedImmersion j.left ∧ IsFinite H.hom ∧ (∀ (T : Over (Sp V)) (x : T ⟶ B), GlobalTheory.MemKL B L x ↔ ∃ z : T ⟶ H, z ≫ j = x) := by
  first | exact @GlobalTheory.KernelRep.exists_finite_closed_kernel
