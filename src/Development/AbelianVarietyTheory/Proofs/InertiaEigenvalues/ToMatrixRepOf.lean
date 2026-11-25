module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RepresentationTheory.Basic
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

noncomputable section

namespace GlobalTheory.PMon

variable {F G ι : Type} [Field F] [Group G] [Fintype ι] [DecidableEq ι]

def repOf (ρ₀ : G →* GL ι F) : Representation F G (ι → F) where
  toFun g := Matrix.toLin' (ρ₀ g : Matrix ι ι F)
  map_one' := by simp; rfl
  map_mul' g h := by simp [Matrix.toLin'_mul]; rfl

@[simp] theorem repOf_apply (ρ₀ : G →* GL ι F) (g : G) (v : ι → F) :
    repOf ρ₀ g v = (ρ₀ g : Matrix ι ι F).mulVec v := rfl

theorem toMatrix_repOf (ρ₀ : G →* GL ι F) (g : G) :
    LinearMap.toMatrix (Pi.basisFun F ι) (Pi.basisFun F ι) (repOf ρ₀ g) = (ρ₀ g : Matrix ι ι F) := by
  rw [LinearMap.toMatrix_eq_toMatrix']
  exact LinearMap.toMatrix'_toLin' _

end GlobalTheory.PMon

end
