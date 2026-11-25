module

public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryUnnSubgroupEqTopOfLeviUnipotentWeyl
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

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel

theorem _root_.GlobalTheory.T.unitaryUnn_subgroup_eq_top_of_leviUnipotentWeyl : ∀ (D : D7) (n : ℕ) (S : Subgroup (GlobalTheory.StdUnn.G D n)), (∀ (g : GlobalTheory.StdUnn.G D n) (a : GL (Fin n) (AE D)), GlobalTheory.StdUnn.mat g = GlobalTheory.StdUnn.blk4 a.1 0 0 (GlobalTheory.MixModel.adj (a⁻¹).1) → g ∈ S) → (∀ (g : GlobalTheory.StdUnn.G D n) (b : Mx D n n), GlobalTheory.StdUnn.mat g = GlobalTheory.StdUnn.blk4 1 b 0 1 → g ∈ S) → (∀ g : GlobalTheory.StdUnn.G D n, GlobalTheory.StdUnn.mat g = GlobalTheory.StdUnn.blk4 0 1 (-1) 0 → g ∈ S) → S = ⊤ := by
  first | exact @GlobalTheory.StdUnn.eq_top_of_levi_unip_weyl
