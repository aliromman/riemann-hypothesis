module
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Formalism.DoubleCosetMeasures.StatementZ
import GroundTheory.AutomorphicForms.GL2.GJMatrixCoord
import Mathlib.Analysis.Matrix.MeasurableSpace

universe u v w

section
variable (m : Type u) (n : Type v) (X : Type w) [MeasurableSpace X]

example : GlobalTheory.SplitWeil.matrixMeasurableSpace (m := m) (n := n) (α := X) =
    Matrix.instMeasurableSpace := by with_reducible rfl

example : GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix (m := m) (n := n) (X := X) =
    Matrix.instMeasurableSpace := by with_reducible rfl

variable [Countable m] [Countable n] [TopologicalSpace X] [BorelSpace X] [SecondCountableTopology X]

example : GroundTheory.Automorphic.GJMatrix.borelSpace_matrix (m := m) (n := n) (X := X) =
    Matrix.instBorelSpaceOfCountableOfSecondCountableTopology m n X := rfl
end

example (m n F : Type) [MeasurableSpace F] :
    Formalism.DoubleCosetMeasures.instMeasMat (m := m) (n := n) (F := F) =
    Matrix.instMeasurableSpace := by with_reducible rfl
