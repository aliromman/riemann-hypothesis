module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
public import GroundTheory.GlobalFields.TateThesis.AdeleMeasurable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFourierRealisesWeylElement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
public import Development.WeilBound.ThetaLifts.SmallCones.IdeleTop
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.Analysis.Matrix.MeasurableSpace

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFock

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem intSchA {κ : Type} [Fintype κ] (m : MeasurableSpace (κ → AF F))
    (hm : m = @MeasurableSpace.pi κ _ fun _ => GroundTheory.Global.measurableSpace_adeleRing F)
    (μ : @Measure (κ → AF F) m) (hμ : @Measure.IsAddHaarMeasure _ _ _ m μ) {φ : (κ → AF F) → ℂ} (hφ : φ ∈ schA F κ) :
    Integrable φ μ := by
  subst hm
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := GroundTheory.Global.measurableSpace_adeleRing F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := GroundTheory.Global.borelSpace_adeleRing F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : BorelSpace (κ → AdeleRing (𝓞 F) F) := Pi.borelSpace
  have h := Measure.isAddLeftInvariant_eq_smul μ (GroundTheory.Automorphic.GJMatrix.adeleMeasurePi F (ι := κ))
  rw [h]
  exact (GlobalTheory.TowU.FourWeyl.integrable_schA hφ).smul_measure (by simp)

theorem measAF_eq : (measAF : MeasurableSpace (AF F)) = GroundTheory.Global.measurableSpace_adeleRing F :=
  (GroundTheory.Global.borelSpace_adeleRing F).measurable_eq.symm

end PositivityTheory.SiegelWeilFormula.KFock

end
