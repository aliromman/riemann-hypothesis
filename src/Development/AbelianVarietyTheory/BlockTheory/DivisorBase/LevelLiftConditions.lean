module

public import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
public import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
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
public import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LevelLiftConditions

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open GlobalTheory.FormTies (levFull)
open scoped TensorProduct

section Level

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

abbrev LevGrp (Dw : Datum H) (l : Level H) : Type := LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l

end Level

variable {D : D7}

def idealHat (D : D7) (I : Ideal (𝓞 D.host.E)) : AddSubgroup (Af D.host.F ⊗[D.host.F] D.host.E) :=
  AddSubgroup.closure {z | ∃ b ∈ I, ∃ y ∈ intAE D, z = ((1 : Af D.host.F) ⊗ₜ (b : D.host.E)) * y}

def IsLevLift {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} (l : Level H) (V : HSp D)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (γ : LevGrp Dw l) (κ : GA D V) : Prop :=
  κ ∈ GfC V ∧ gLat V κ = (latHat V : Set _) ∧
    ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
    ∀ a' ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      (l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).mkQ a' = γ ((l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).mkQ a) →
      ∃ w ∈ latGHat V 1, (finHom V κ).1.mulVec (finVec V (ι a)) - finVec V (ι a') = (l.M : ℕ) • w

end GlobalTheory.IndefiniteRowSideFullHecke.LevelLiftConditions
