module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SphericalOfHasSat

@[expose] public section




section
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.Zero.LLC UpperTheory.V.Af UpperTheory.V.Z.Gam
open UpperTheory.GalN.V GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
namespace UpperTheory.V.Z.Win
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
def AIsoTwAlt : Prop :=
  _root_.UpperTheory.V.Af.Hypotheses' → ∀ (F Ω : Type) [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)), WitA ι r →
    (∀ r', RepIso r r' → WitA ι r') ∧ ∀ μ : G F Ω →* (Qbar l)ˣ, IsAlgChar ι μ → WitA ι (tw r μ)
def AUpDownAlt : Prop :=
  _root_.UpperTheory.V.Af.HypothesesH' → RowT → ∀ (F K Ω : Type) [Field F] [NumberField F] [IsCMField F] [Field K] [NumberField K] [IsCMField K] [Field Ω]
    [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsGalois F K], Group.IsSolvable (K ≃ₐ[F] K) →
    ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ r : G F Ω →* GL (Fin n) (Qbar l), Continuous r →
    IsIrr (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) → Sol.Pol ι r → IsRegAlgAutomorphicAttached ι r → Flagged r →
      (WitA ι r → WitA ι (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω))) ∧
      (IneAb r → Keeps r K → WitA ι (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) → WitA ι r)
end UpperTheory.V.Z.Win
end
end
