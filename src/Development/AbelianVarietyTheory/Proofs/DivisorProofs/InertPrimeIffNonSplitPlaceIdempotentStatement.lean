module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPrimeIffNonSplitPlaceIdempotent
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCongLevelIntG

@[expose] public section

open NumberField MeasureTheory IsDedekindDomain
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.BotClassDict (finQ)


theorem _root_.GlobalTheory.T.inertPrime_iff_nonSplitPlaceIdempotent : ∀ (D : D7) (q : ℕ), q.Prime → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (η : AF D.host.F), IsPlaceIdem D v η →
  (q : 𝓞 D.host.F) ∈ v.asIdeal → (Formalism.MainNotions.StandardLatticesGL3.InertQ D q ↔ GlobalTheory.WeilParts.NonSplitAt D v η) := by
  first | exact @GlobalTheory.InertPlace.inertQ_iff_nonSplitAt
