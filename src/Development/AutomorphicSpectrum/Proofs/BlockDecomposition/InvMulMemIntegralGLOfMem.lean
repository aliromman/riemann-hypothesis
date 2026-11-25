module

import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.MinusculeCentralEigen
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.FormQuasiInvariantMirabolic
import GroundTheory.AutomorphicForms.HaarCosets
public import GroundTheory.AutomorphicForms.MacdonaldHecke
public import GroundTheory.AutomorphicForms.MacdonaldWhittakerHecke
import GroundTheory.LocalFields.LocalFourierHaar
import Mathlib.RingTheory.Henselian
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Separation.Connected

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

open MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa
  GroundTheory.Automorphic.Spherical HeckeAlgebra PositivityTheory.JacquetShalikaLocal
open ValuativeRel (valuation)
open scoped ValuativeRel Pointwise

namespace GlobalTheory.CompanionTheory.SatakeBound

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

local notation "π" => (GLnLocal.uniformizer F : F)

section Hecke

variable {V : Type} [AddCommGroup V] [Module ℂ V]
  [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]

end Hecke

theorem heckeEigenvector_whittaker : L7 := by
  apply PositivityTheory.JacquetShalikaLocal.minuscule_eigenvalue

end GlobalTheory.CompanionTheory.SatakeBound

end
