module
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Formalism.DoubleCosetMeasures.StatementZ
import GroundTheory.AutomorphicForms.GL2.GJMatrixCoord

open scoped Formalism.DoubleCosetMeasures

universe u v w
variable (m : Type u) (n : Type v) (X : Type w) [MeasurableSpace X]
variable [Countable m] [Countable n] [TopologicalSpace X] [BorelSpace X] [SecondCountableTopology X]

#synth MeasurableSpace (Matrix m n X)
#synth BorelSpace (Matrix m n X)

example : (inferInstance : MeasurableSpace (Matrix m n X)) = Matrix.instMeasurableSpace := by
  with_reducible rfl
