module

public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtensionUnramifiedAtOnePlace
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ArtEx
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

@[expose] public section

open NumberField IsDedekindDomain

theorem UpperTheory.Zero.LLC.extEx :
    UpperTheory.Zero.LLC.ExtEx := by
  intro E Ω _ _ _ _ _ A w h g _ i hi n hn
  obtain ⟨E', fE, nE, _, aE, aΩ, tE, cE, w', h', hg, unr, card, _, _⟩ :=
    _root_.GlobalTheory.UnrCycExt.exists_unramified_ext E Ω g A w h i hi n hn
  obtain ⟨a', ha', _⟩ := UpperTheory.Zero.LLC.artEx E' Ω A w' h'
  haveI : w'.asIdeal.IsMaximal := w'.isMaximal
  letI : Field (𝓞 E' ⧸ w'.asIdeal) := Ideal.Quotient.field _
  haveI : CharP (𝓞 E' ⧸ w'.asIdeal) g := by
    rw [CharP.charP_iff_prime_eq_zero (Fact.out : Nat.Prime g)]
    rw [← map_natCast (Ideal.Quotient.mk w'.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact hg
  letI : Algebra (ZMod g) (𝓞 E' ⧸ w'.asIdeal) := ZMod.algebra _ g
  exact ⟨UpperTheory.Zero.LLC.Ext.mk E' w' h' unr card a' ha' (𝓞 E' ⧸ w'.asIdeal)
    (Ideal.Quotient.mk w'.asIdeal) Ideal.Quotient.mk_surjective (Ideal.mk_ker)⟩
