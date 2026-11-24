module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
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

@[expose] public section

namespace KStar.Ram

open NumberField DirichletCharacter IsCyclotomicExtension.Rat

noncomputable def fieldUnits (N : ℕ) [NeZero N] {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {N} ℚ K] (E : IntermediateField ℚ K) : Subgroup (ZMod N)ˣ :=
  E.fixingSubgroup.map (galEquivZMod N K).toMonoidHom

noncomputable def fieldChars (N : ℕ) [NeZero N] {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {N} ℚ K] (E : IntermediateField ℚ K) :
    Subgroup (DirichletCharacter ℂ N) :=
  annihilator ℂ (fieldUnits N E : Set (ZMod N)ˣ)


open Classical in
noncomputable def rootWeight (l m : ℕ) : ℚ := by
  classical
  exact if m ≠ 1 ∧ ∃ s, m = l ^ s then 1 / (Nat.totient m : ℚ) else 0

end KStar.Ram
