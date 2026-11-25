module

public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplexConjugationMapsMultiplicitySpace
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
import Formalism.LocalToGlobal.Divisibility.DefGroup
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace

theorem _root_.GlobalTheory.T.complexConjugation_maps_multiplicitySpace : ∀ {D : D7} {V : HSp D} {S S' : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c τ (M'.rep τ g w) = M.rep τ g (c τ w)) → (∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ) ∧ ∀ J χ, ∀ T ∈ Mult θ M J χ, ∃ T' ∈ Mult θ M' J (fun k => star (χ k)), ∀ (v' : M'.Vec) (v : M.Vec), (∀ τ, (v τ : M.H τ) = c τ (v' τ)) → ∀ g, T' v' g = star (T v g) := by
  first | exact @GlobalTheory.ConjMult.conj_mult
