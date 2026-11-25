module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaBasicK
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



section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {m n : ℕ}
variable {Y : Spc F E n} {A : Spc F E m}
local instance  (v : Pl F) : IsNonarchimedeanLocalField (Fv F v) := GlobalTheory.LocalData.isLocalField v
def SplitModel_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s' → ∀ (v : Pl F) (t : E →ₐ[F] Fv F v), (∃ ι, M.IsLinW B.ψ t 1 1 ι) ∧ ∀ ι, M.IsLinW B.ψ t 1 1 ι →
      ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ (g₀ : GL (Fin n) (Fv F v)) (h₀ : GL (Fin d) (Fv F v)),
        g₀.1 = (mat g).map (piW t) → h₀.1 = (mat h).map (piW t) → ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _, Acts (evFin F v) (om (g, h)) φ φ₁ →
          ι φ₁ = GlobalTheory.SplitFlip.omA (chrW χW t)⁻¹ (chrW χX t) g₀ h₀ (ι φ)
end GlobalTheory.ThK.Dbl
end
end
