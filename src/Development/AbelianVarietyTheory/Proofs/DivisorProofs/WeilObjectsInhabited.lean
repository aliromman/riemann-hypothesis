module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactOpenAddSubgroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantAddChar
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Separation.Connected

@[expose] public section

noncomputable section

open MeasureTheory Matrix ValuativeRel
open scoped NNReal Topology Kronecker

namespace GlobalTheory.WeilM

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {α β κ : Type}

theorem invariant_comp_mulVec [Fintype κ] [DecidableEq κ] (m : ((κ → F) → ℂ) →ₗ[ℂ] ℂ)
    (hm : ∀ φ ∈ SB (κ → F), ∀ a, m (fun x => φ (x + a)) = m φ) (g : GL κ F) {φ : (κ → F) → ℂ} (hφ : φ ∈ SB (κ → F))
    (hφ' : (fun x => φ (g.val.mulVec x)) ∈ SB (κ → F)) :
    ((distribHaarChar F (GeneralLinearGroup.det g) : ℝ) : ℂ) * m (fun x => φ (g.val.mulVec x)) = m φ := by
  borelize F
  have := SplitWeil.secondCountable F
  have := SplitWeil.t2Space F
  have := nonarch_pi F κ
  obtain ⟨c, hc⟩ := GlobalTheory.WeilM.HaarUniq.exists_eq_mul_integral (κ → F) (Measure.pi fun _ => (Measure.addHaar : Measure F)) m hm
  rw [hc _ hφ, hc _ hφ', mul_left_comm, integral_comp_mulVec]

variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] [Invertible (2 : F)]

section Pair

variable {R : Type} [CommRing R]



end Pair

end GlobalTheory.WeilM

end
