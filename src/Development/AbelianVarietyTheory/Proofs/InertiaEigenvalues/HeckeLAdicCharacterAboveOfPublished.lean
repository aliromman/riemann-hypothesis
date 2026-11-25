module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterCrystalline
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfIsNilpotentOfFinrankEqOne
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.Published

namespace GlobalTheory.HeckeAboveBridge

theorem heckeLAdicCharacterAbove_of_potSemistable :
    HeckeLAdicCharacterDeRham → HeckeLAdicCharacterCrystalline → DeRhamPotSemistable →
      HeckeLAdicCharacterAbove := by
  intro hdR hcr hpst
  rw [heckeLAdicCharacterAbove_iff]
  intro E Ω _ _ _ _ _ l _ P AI hT ι art hart χ n μ hχ hμ hl w A hA O _ _ _ Bw hB
  have h1 := hdR E Ω l P AI hT ι art hart χ n μ hχ hμ hl w A hA O Bw hB
  exact ⟨h1.1, GlobalTheory.PotCrysRankOne.isPotCrystalline_of_deRham_character hpst E Ω l P AI hT μ hμ A O Bw hB h1.1,
    hcr E Ω l P AI hT ι art hart χ n μ hχ hμ hl w A hA O Bw hB, h1.2⟩

end GlobalTheory.HeckeAboveBridge

end
