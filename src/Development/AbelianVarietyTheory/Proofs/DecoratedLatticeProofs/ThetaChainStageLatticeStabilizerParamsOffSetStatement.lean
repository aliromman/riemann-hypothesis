module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageLatticeStabilizerParamsOffSet
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto

theorem _root_.GlobalTheory.T.thetaChainStage_lattice_stabilizer_params_off_set : ∀ D : D7, ForStage D fun c _ s => (∀ v ∉ c.S, GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v = GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram (GlobalTheory.AdelicU.frameLat s.V) v) ∧ ∀ (f : GA D s.V → ℂ) (B : GlobalTheory.LFun.Fam D.host.E), GlobalTheory.LFun.IsParamFun D.sp.cm.sig s.V.gram s.Λ (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) f B ↔ GlobalTheory.LFun.IsParamFunV s.V c.S f B := by
  first | exact @GlobalTheory.ChainOnto.stabLoc_isParamFun_frameLat
