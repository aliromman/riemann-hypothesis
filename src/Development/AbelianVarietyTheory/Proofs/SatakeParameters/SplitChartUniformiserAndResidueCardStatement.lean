module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitChartUniformiserAndResidueCard
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
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct

theorem _root_.GlobalTheory.T.splitChart_uniformiser_and_residueCard : ∀ {D : D7} (e : AE D) (P : HeightOneSpectrum (𝓞 D.host.E)) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsIdemAt e P → Chart e v π → ∀ ϖ : 𝓞 D.host.E, ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → (∃ p : Ov D v, algebraMap (Ov D v) (Fv D.host.F v) p = π (incA D (ϖ : D.host.E)) ∧ Irreducible p) ∧ Nat.card (IsLocalRing.ResidueField (Ov D v)) = Ideal.absNorm P.asIdeal := by
  first | exact @GlobalTheory.SplitUnif.unif_chart
