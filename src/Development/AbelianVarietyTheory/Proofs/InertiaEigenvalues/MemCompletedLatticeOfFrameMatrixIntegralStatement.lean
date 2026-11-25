module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCompletedLatticeOfFrameMatrixIntegral
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open Classical



theorem _root_.GlobalTheory.T.mem_completedLattice_of_frameMatrix_integral : ∀ {D : D7} {S T : HSp D} {F : Frame S T}, F.Good → ∀ {R : Finset (Pl D.host.E)}, PlacesOK ∅ R → ∀ {x : WO S T}, IsHalf (idem R) x → IsIntM (frMapO S T F.βS F.βT x) → x ∈ F.lat := by
  first | exact @GlobalTheory.IntHalfLat.mem_lat_of_frMapO_int
