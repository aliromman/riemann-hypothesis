module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertSph

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def latAt {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) : AddSubgroup (Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  AddSubgroup.closure {z | ∃ a : AF F, At (evFin F v) a ∧ evFin F v a ∈ v.adicCompletionIntegers F ∧
    ∃ y ∈ W.L, z = a • fun i => inclR (F := F) (AF F) (y i)}

def KAt (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) : Set (UA σ W.J) :=
  {h | h ∈ UAt σ W (evFin F v) ∧ ∀ z ∈ latAt W v, mat h *ᵥ z ∈ latAt W v ∧ mat h⁻¹ *ᵥ z ∈ latAt W v}

theorem one_mem_KAt (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) : (1 : UA σ W.J) ∈ KAt σ W v := by
  refine ⟨?_, fun z hz => ?_⟩
  · intro u _
    show u • (mat (1 : UA σ W.J) - 1) = 0
    simp [mat]
  · simp [mat, hz]

end GlobalTheory.InertSph
