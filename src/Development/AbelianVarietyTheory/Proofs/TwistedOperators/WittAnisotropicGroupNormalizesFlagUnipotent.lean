module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct

namespace GlobalTheory.MixPer

theorem witt_anisotropic_group_normalizes_flag_unipotent : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), ∀ n ∈ flagN d, ∀ h : GA D S₀,
    d.emb0 h * n * (d.emb0 h)⁻¹ ∈ flagN d := by
  intro D S S₀ ρ d n hn h
  have he : Formalism.L2.Theta.mt S (d.emb0 h) ⬝ d.e.map (incA D) = d.e.map (incA D) := d.wittDecomp_anisotropicEmbedding_inclX h
  have he' := GlobalTheory.BesselChar.inv_fix_cols (GlobalTheory.BesselChar.mt_inv_mul S (d.emb0 h)) he
  unfold flagN at hn ⊢
  rw [GlobalTheory.BesselChar.mem_NFlag_iff S d.e (isIsoSub_e d).1] at hn ⊢
  rw [GlobalTheory.BesselChar.mt_mul, GlobalTheory.BesselChar.mt_mul]
  exact hn.conj he he' (GlobalTheory.BesselChar.mt_mul_inv S _) (GlobalTheory.BesselChar.perp_fixed d.e _ he')

end GlobalTheory.MixPer
