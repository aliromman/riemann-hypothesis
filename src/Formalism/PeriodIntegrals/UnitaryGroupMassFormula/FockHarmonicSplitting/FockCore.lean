module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockHarmonicSplitting.FockInnerSelfReNonneg

@[expose] public section

noncomputable section

open MvPolynomial

namespace PI.FHS

variable {σ : Type*}

def FockV (σ : Type*) : Type _ := MvPolynomial σ ℂ

instance : AddCommGroup (FockV σ) := inferInstanceAs (AddCommGroup (MvPolynomial σ ℂ))

instance : Module ℂ (FockV σ) := inferInstanceAs (Module ℂ (MvPolynomial σ ℂ))

@[instance_reducible]
def fockCore : InnerProductSpace.Core ℂ (FockV σ) where
  inner P Q := FockH1Action.fockInner (σ := σ) P Q
  conj_inner_symm x y := fockInner_conj (σ := σ) x y
  re_inner_nonneg x := by simpa using fockInner_self_re_nonneg (σ := σ) x
  add_left x y z := fockInner_add_left (σ := σ) x y z
  smul_left x y r := fockInner_smul_left (σ := σ) r x y
  definite _ h := fockInner_self_eq_zero (σ := σ) h

lemma exists_orth [Fintype σ] (K : Submodule ℂ (MvPolynomial σ ℂ)) (n : ℕ)
    (hK : K ≤ FockH1Action.homog σ n) (f : MvPolynomial σ ℂ) :
    ∃ y ∈ K, ∀ x ∈ K, FockH1Action.fockInner x (f - y) = 0 := by
  classical
  have hhom : FiniteDimensional ℂ (FockH1Action.homog σ n) :=
    Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg σ ℂ n)
  have hfin : FiniteDimensional ℂ K := Submodule.finiteDimensional_of_le hK
  let K' : Submodule ℂ (FockV σ) := K
  have : FiniteDimensional ℂ K' := hfin
  let _ : NormedAddCommGroup (FockV σ) := (fockCore (σ := σ)).toNormedAddCommGroup
  let _ : InnerProductSpace ℂ (FockV σ) := InnerProductSpace.ofCore (fockCore (σ := σ)).toCore
  let g : FockV σ := f
  let y := K'.orthogonalProjectionOnto g
  exact ⟨(y : FockV σ), y.property, (K'.mem_orthogonal _).1 (K'.sub_starProjection_mem_orthogonal g)⟩

end PI.FHS
