module

public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChevalleyUnits
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalArtinLocalIdeleInjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinExistsHolds
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import CompanionTheory.AutomorphicTheory.PlaceSeparation.IsOpenQuotientMapArt0
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

theorem UpperTheory.Zero.LLC.artEx :
    UpperTheory.Zero.LLC.ArtEx := by
  intro E Ω _ _ _ _ _ A w h
  obtain ⟨a, ha⟩ := GlobalTheory.localArtinExists_holds E Ω A w h
  refine ⟨a, ha, fun b hb => ?_⟩
  obtain ⟨art, hart⟩ := _root_.CompanionTheory.FamInh.globalArtin E Ω
  have hinj := GlobalTheory.ArtinLocalInj.artin_localIdele_injective GlobalTheory.Published.chevalleyUnits' E Ω art hart w
  refine MonoidHom.ext fun σ => hinj ?_
  exact (hb.glob art hart σ).trans (ha.glob art hart σ).symm
