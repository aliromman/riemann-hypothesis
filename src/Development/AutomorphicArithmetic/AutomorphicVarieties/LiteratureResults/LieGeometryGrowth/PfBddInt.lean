module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PairDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure
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

open UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Lit.Geo.Pf.bddInt :
    UpperTheory.V.Lit.Geo.Pf.BddInt := by
  intro E _ _ _ a μ _ F hF ⟨C, hC⟩
  haveI := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  have h := GlobalTheory.CuspQuot.memL2_of_bound (μ := μ) hF.cont
    (GlobalTheory.CuspRep.CuspidalL2GL.leftInv_latticeGL hF.left hF.centre) hC
  exact ⟨h.2.integrable one_le_two, h⟩
