module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Trace

public section

/-- The trace on a finite product is the sum of the traces of the diagonal blocks. -/
theorem LinearMap.trace_pi {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, FiniteDimensional K (V i)] (f : Module.End K (∀ i, V i)) :
    LinearMap.trace K _ f =
      ∑ i, LinearMap.trace K _ (LinearMap.proj i ∘ₗ f ∘ₗ LinearMap.single K V i) := by
  have hf : f = ∑ i, LinearMap.single K V i ∘ₗ (LinearMap.proj i ∘ₗ f) := by
    apply LinearMap.ext
    intro x
    simp [Finset.univ_sum_single]
  conv_lhs => rw [hf, map_sum]
  exact Finset.sum_congr rfl fun i _ => LinearMap.trace_comp_comm' _ _
