module

public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPinsRec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHarmonicCoefficientMapAtWeights
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

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace

theorem _root_.GlobalTheory.T.exists_harmonicCoefficientMap_at_weights : ∀ (D : D7) (Q : Formalism.L2.Pj.Par D), Q.Pins → ∀ (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)), KapIs κ → ∀ (i : Fin D.R.m) (c' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff Q.l), ∃ (io : VsV D i c'.F →ₗ[c'.F] MvPolynomial (LtN (Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) c'.F) (hw : VsV D i c'.F), IoLFRec c' (fun τ => embF c' (tauE D τ)) (lamV D i) (wtA (κ i)) io hw := by
  first | exact @GlobalTheory.CoefMapRecord.exists_io_record
