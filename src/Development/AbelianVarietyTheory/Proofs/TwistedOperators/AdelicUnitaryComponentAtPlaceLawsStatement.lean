module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicUnitaryComponentAtPlaceLaws
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder


theorem _root_.GlobalTheory.T.adelicUnitaryComponentAtPlace_laws : ∀ (D : D7), (∀ (V : HSp D) (p : Place D) (g : GA D V), Formalism.L2.Theta.mt V (gAt V p g) = idem D p • Formalism.L2.Theta.mt V g + (1 - idem D p) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) ∧ gAt V p (gAt V p g) = gAt V p g ∧ ∀ q, q ≠ p → gAt V q (gAt V p g) = 1) ∧ ∀ (S T : HSp D) (p : Place D) (g : GA D S) (h : GA D T) (w : WO S T), actO S T (gAt S p g) (gAt T p h) w = idem D p • actO S T g h w + (1 - idem D p) • w ∧ wAt p (actO S T g h w) = actO S T (gAt S p g) (gAt T p h) (wAt p w) := by
  first | exact @GlobalTheory.PlaceComponent.gAt_laws
