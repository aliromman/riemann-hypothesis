module
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
@[expose] public section
open Matrix Topology
noncomputable section
namespace GlobalTheory.LGrp
variable {k n : Type} [Field k] [Fintype n] [DecidableEq n] [TopologicalSpace k] [IsTopologicalRing k] [T2Space k] [LocallyCompactSpace k]
example : LocallyCompactSpace (GL n k) := inferInstance
end GlobalTheory.LGrp
