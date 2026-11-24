module

import Formalism.DoubleCosetMeasures.StatementZ
import GroundTheory.AutomorphicForms.GL2.GJMatrixCoord

open Matrix
open scoped Formalism.DoubleCosetMeasures

section
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n : ℕ)

example : (inferInstance : MeasurableSpace (GL (Fin n) K)) =
    Formalism.DoubleCosetMeasures.instMeasGL (K := K) n := by
  with_reducible rfl

example : @BorelSpace (GL (Fin n) K) _ (Formalism.DoubleCosetMeasures.instMeasGL (K := K) n) :=
  Formalism.DoubleCosetMeasures.instBorelGL n

end

#synth MeasurableSpace (GL (Fin 2) ℝ)
#synth BorelSpace (GL (Fin 2) ℝ)
