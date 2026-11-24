module
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
@[expose] public section
open MeasureTheory ValuativeRel Matrix Topology
open scoped NNReal ENNReal Pointwise
noncomputable section
namespace GlobalTheory.SplitFlip
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type*} [Fintype n] [DecidableEq n]
example : SecondCountableTopology (GL n k) := inferInstance
example : LocallyCompactSpace (GL n k) := inferInstance
example : T2Space (GL n k) := inferInstance
end GlobalTheory.SplitFlip
