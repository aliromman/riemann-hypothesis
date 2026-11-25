module

public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.ColNorms

theorem liftFr_lifts : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (ST SG : Finset (HeightOneSpectrum (𝓞 E))) (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (w : SG), (∀ x, d.1.liftFr w x ∈ d.1.at w.1 ↔ x ∈ stdAt E n w.1) ∧ ∀ x ∈ stdAt E n w.1, d.1.be w (d.1.liftFr w x) = redV w.1 x :=
  fun _ _ _ _ _ _ _ d w => GlobalTheory.TopStep.liftFr_spec d.2 w

end GlobalTheory.ColNorms
