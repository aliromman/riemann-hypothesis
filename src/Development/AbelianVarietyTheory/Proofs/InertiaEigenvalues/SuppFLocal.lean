module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainLevelProperties
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Datum

noncomputable section

namespace GlobalTheory.SuppLocal

theorem suppF_local : ∀ (D : D7) (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e f : AE D) (k : GA D V),
    IsPrimeIdem P e f → SuppF V f k → k ∈ GfC V ∧ ∀ v : HeightOneSpectrum (𝓞 D.host.F), v ≠ P.under (𝓞 D.host.F) →
      GlobalTheory.FinZeta.projV V v k = 1 := by
  intro D V P e f k h hk
  obtain ⟨x, rfl⟩ := (GlobalTheory.AdelicU.Supp.suppF_iff_of_isPrimeIdem V h rfl k).1 hk
  exact ⟨GlobalTheory.ChainOnto.LevelFacts.emb_mem_GfC V _ x, fun v hv => GlobalTheory.AdelicU.proj_emb_ne _ _ hv x⟩

end GlobalTheory.SuppLocal
