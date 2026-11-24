module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
public import GroundTheory.GlobalFields.ClassFieldConsequences.HilbertClassField
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

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base

namespace UpperTheory.V.Kum

def artCl (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] : G K Ω →* ClassGroup (𝓞 K) :=
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  (GroundTheory.Global.hilbertClassFieldArtinEquiv K Ω).symm.toMonoidHom.comp (AlgEquiv.restrictNormalHom _)

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]
  (K : Type) [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] {U : Subgroup (G F Ω)}

def artU (hU : U ≤ galOf F K Ω) : U →* ClassGroup (𝓞 K) := (artCl K Ω).comp (toGal K hU)

def clPull (hU : U ≤ galOf F K Ω) (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] :
    (ClassGroup (𝓞 K) → M) →ₗ[R] (U → M) :=
  LinearMap.funLeft R M (artU K hU)

theorem clPull_apply (hU : U ≤ galOf F K Ω) (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]
    (θ : ClassGroup (𝓞 K) → M) (u : U) : clPull K hU R M θ u = θ (artCl K Ω (toGal K hU u)) := rfl

end UpperTheory.V.Kum

end
