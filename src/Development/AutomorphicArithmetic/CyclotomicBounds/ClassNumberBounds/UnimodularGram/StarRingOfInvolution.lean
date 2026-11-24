module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Module.LinearMap.Star
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.LinearAlgebra.BilinearMap
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
import Mathlib.Tactic.TypeStar
public import Mathlib.LinearAlgebra.Dual.Defs

@[expose] public section

namespace KStar.Cstarloc

structure UnramDatum (R : Type*) [CommRing R] [StarRing R] : Prop where
  trace_one : ∃ e : R, e + star e = 1
  norm_onto : ∀ u : R, IsUnit u → star u = u → ∃ a : R, a * star a = u

variable {R : Type*} [CommRing R] [StarRing R] {M : Type*} [AddCommGroup M] [Module R M]

abbrev Sesq (R : Type*) [CommRing R] [StarRing R] (M : Type*) [AddCommGroup M] [Module R M] :=
  M →ₗ[R] M →ₗ⋆[R] R

def IsHerm (h : Sesq R M) : Prop := ∀ x y, h y x = star (h x y)

def IsUnimod (h : Sesq R M) : Prop := Function.Bijective (h.flip : M → Module.Dual R M)

def gram {ι : Type*} (h : Sesq R M) (b : ι → M) : Matrix ι ι R := Matrix.of fun i j => h (b i) (b j)

def IsOrthonormal {ι : Type*} [DecidableEq ι] (h : Sesq R M) (b : ι → M) : Prop := gram h b = 1

def perp (h : Sesq R M) (x : M) : Submodule R M := LinearMap.ker (h.flip x)

def restr (h : Sesq R M) (N : Submodule R M) : Sesq R N := h.domRestrict₁₂ N N

theorem mem_perp (h : Sesq R M) (x y : M) : y ∈ perp h x ↔ h y x = 0 := by
  rw [perp, LinearMap.mem_ker, LinearMap.flip_apply]

end KStar.Cstarloc
