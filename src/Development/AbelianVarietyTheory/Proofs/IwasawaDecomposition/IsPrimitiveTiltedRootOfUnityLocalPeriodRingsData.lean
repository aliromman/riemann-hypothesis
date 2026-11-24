module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
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

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem core_isEps : ∀ (l : ℕ) [Fact l.Prime], ∀ C : Core l, IsEps C.ε := by
  intro l _ C
  refine ⟨?_, ?_⟩
  · have h := C.ε_root 0
    rw [C.ζ_zero, map_one] at h
    exact Subtype.ext h
  · intro h1
    have h := C.ε_root 1
    have h2 : rootT C.ε 1 = 1 := h1
    rw [h2] at h
    apply C.ζ_one
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [map_one, ← h]
    rfl

end GlobalTheory.MemLoc
