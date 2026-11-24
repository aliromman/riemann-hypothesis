module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.AdelicUnitaryHaarMeasure
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ArchimedeanUnitaryGroupStabilisersUnimodular
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

@[expose] public section

namespace GlobalTheory.LocalUnitaryUnimod

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure

theorem unimodularOver_adicCompletion :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E),
      IsHermND σ J → ∀ v : HeightOneSpectrum (𝓞 F), UnimodularOver (Fv F v) σ J := by
  intro F E _ _ _ _ _ σ hσ M J hJ v
  have := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  exact GlobalTheory.ArchUnitaryUnimod.unimodularOver_of_artinian (Fv F v) hσ hJ

end GlobalTheory.LocalUnitaryUnimod
