module

import Main

set_option autoImplicit false

namespace ProtectedMatrixCheck

def RiemannZetaZerosOnLine : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s ≠ 1 → s.re = 1 / 2

def DirichletLNonvanishingRightOfHalf : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

def DirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

def PrimitiveDirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

example : _root_.RiemannZetaZerosOnLine = ProtectedMatrixCheck.RiemannZetaZerosOnLine := rfl

example : _root_.DirichletLNonvanishingRightOfHalf = ProtectedMatrixCheck.DirichletLNonvanishingRightOfHalf := rfl

example : _root_.DirichletLZerosOnLine = ProtectedMatrixCheck.DirichletLZerosOnLine := rfl

example : _root_.PrimitiveDirichletLZerosOnLine = ProtectedMatrixCheck.PrimitiveDirichletLZerosOnLine := rfl

example : _root_.RiemannHypothesis := _root_.riemannHypothesis

example : ProtectedMatrixCheck.RiemannZetaZerosOnLine := _root_.riemannZeta_eq_zero_re

example : ProtectedMatrixCheck.DirichletLNonvanishingRightOfHalf := _root_.LFunction_ne_zero_of_half_lt_re

example : ProtectedMatrixCheck.DirichletLZerosOnLine := _root_.LFunction_eq_zero_re

example : ProtectedMatrixCheck.PrimitiveDirichletLZerosOnLine := _root_.LFunction_eq_zero_re_of_isPrimitive

end ProtectedMatrixCheck

#print axioms riemannHypothesis
#print axioms riemannZeta_eq_zero_re
#print axioms LFunction_ne_zero_of_half_lt_re
#print axioms LFunction_eq_zero_re
#print axioms LFunction_eq_zero_re_of_isPrimitive
