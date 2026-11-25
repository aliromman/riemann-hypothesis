module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
import GroundTheory.LocalFields.PadicLogSeries
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

open GlobalTheory.CuspRep GlobalTheory.PRep

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.adm :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.admitted := by
  intro E _ _ _ n w τ U hU
  letI := GlobalTheory.LocalData.complRel w
  haveI := GlobalTheory.LocalData.isLocalField w
  have hadm := PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top (w.adicCompletion E) n τ.V τ.ρ τ.smooth τ.irred
  obtain ⟨ho, hc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n
  have hsmall : FiniteDimensional ℂ (fixed τ.ρ (U ⊓ GlobalTheory.LFun.KGL w (n := n))) :=
    hadm.2 _ (hU.inter ho) (hc.inter_left (U.isClosed_of_isOpen hU))
  have hle : fixed τ.ρ U ≤ fixed τ.ρ (U ⊓ GlobalTheory.LFun.KGL w (n := n)) := fun v hv h => hv ⟨h.1, h.2.1⟩
  exact Submodule.finiteDimensional_of_le hle
