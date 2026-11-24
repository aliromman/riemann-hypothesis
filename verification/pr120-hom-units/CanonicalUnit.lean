module

public import Mathlib

@[expose] public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj

theorem canonicalHomNumeral {C : Type*} [Category C] [CartesianMonoidalCategory C]
    (X M : C) [MonObj M] :
    (⟨toUnit X ≫ η⟩ : OfNat (X ⟶ M) 1) = (inferInstance : OfNat (X ⟶ M) 1) := rfl

theorem canonicalHomUnit {C : Type*} [Category C] [CartesianMonoidalCategory C]
    (X M : C) [MonObj M] :
    (1 : X ⟶ M) = toUnit X ≫ η := Hom.one_def

#print axioms canonicalHomNumeral
#print axioms canonicalHomUnit
