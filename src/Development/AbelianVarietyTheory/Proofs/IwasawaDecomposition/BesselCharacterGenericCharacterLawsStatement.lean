module

public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedBessel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

theorem _root_.GlobalTheory.T.besselCharacter_generic_character_laws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V), HSpace.IsIsomEmb A B ι → ∀ d : BesDat A B ι, (∀ n n' : NFlag B d.e, besChar ψ d ((n * n' : NFlag B d.e) : GA D B) = besChar ψ d (n : GA D B) * besChar ψ d (n' : GA D B)) ∧ (∀ γ ∈ NFlagQ B d.e, besChar ψ d (γ : GA D B) = 1) ∧ (Continuous fun n : NFlag B d.e => besChar ψ d (n : GA D B)) ∧ ∀ g h, EmbRel B A ι g h → ∀ n ∈ NFlag B d.e, g * n * g⁻¹ ∈ NFlag B d.e ∧ besChar ψ d (g * n * g⁻¹) = besChar ψ d n := by
  first | exact @GlobalTheory.BesselChar.besChar_laws
