module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteIffTateModuleMapInjectiveAndIsogenyIffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFlatFinrank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDetEqInvCardCokerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleFreeFinrankTwoMulDim
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleMapInjectiveCardCokerOfIsogenyStatement
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

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar

namespace GlobalTheory.AV.AbVar

theorem norm_natCast_padicInt (l : ℕ) [Fact l.Prime] {n : ℕ} (hn : n ≠ 0) :
    ‖((n : ℕ) : ℤ_[l])‖ = (l : ℝ) ^ (-(padicValNat l n : ℤ)) := by
  rw [PadicInt.norm_def]
  push_cast
  have h := Padic.eq_padicNorm (p := l) (n : ℚ)
  push_cast at h
  rw [h, padicNorm.eq_zpow_of_ne_zero (by exact_mod_cast hn)]
  push_cast
  rw [Nat.padicValNat_def, padicValRat_of_nat]

theorem norm_deg_eq_norm_det : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (A : AbVar K) (f : End A),
    ‖((deg (A := A) (B := A) f.asHom : ℕ) : ℤ_[l])‖ = ‖LinearMap.det (tend l A f)‖ := by
  intro K _ l _ hl A f
  obtain ⟨hfree, hfin, -, hVfin, -⟩ := tl_free_finrank K l hl A
  by_cases hf : IsIsogeny (A := A) (B := A) f.asHom
  · obtain ⟨-, -, hpos, -⟩ := isogeny_flat_finrank K A A f.asHom hf
    obtain ⟨-, hcard⟩ := _root_.GlobalTheory.AV.AbVar.tmap_injective_card_coker_of_isIsogeny K l hl A A f.asHom hf
    have hdet := _root_.GlobalTheory.DetIndexPadic.norm_det_eq_of_card_coker l (Tl l A)
      (tmap l A A f.asHom) (padicValNat l (deg f.asHom)) hcard
    change _ = ‖LinearMap.det (tmap l A A f.asHom)‖
    rw [hdet, norm_natCast_padicInt l hpos.ne']
  · have hdeg : deg (A := A) (B := A) f.asHom = 0 := by rw [deg, ite_eq_right hf]
    rw [hdeg, Nat.cast_zero, norm_zero, eq_comm, norm_eq_zero]
    by_contra hne
    apply hf
    rw [(GlobalTheory.T.isFinite_iff_tateModuleMap_injective_and_isogeny_iff K l hl A A f.asHom).2]
    have hu : IsUnit (LinearMap.det (vmap l f.asHom)) := by
      rw [vmap, LinearMap.det_baseChange]
      exact (isUnit_iff_ne_zero).2 ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective ℤ_[l] ℚ_[l])).2 hne)
    rw [← LinearMap.isUnit_iff_isUnit_det] at hu
    exact (Module.End.isUnit_iff _).1 hu

end GlobalTheory.AV.AbVar
