module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsFirstChernClassInFamily
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapUSharp
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.ExistsEpsPeriodTUnit
import GroundTheory.PAdicHodge.FontaineLemmaPeriod
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

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory GroundTheory.PAdicHodge Formalism.Per6

namespace CrystallineSemistableComparison.HT

variable (l : ℕ) [Fact l.Prime]

theorem eps_tA : ∃ (ε : B.Eps l) (u : Acris l), tA l = ε.μ * u := by
  obtain ⟨u, hu, e⟩ := ACris.exists_periodT_eq_mu_mul_unit (K := ℂ_[l]) (p := l) (untilt_epsilon (p := l))
    untilt_frobeniusEquiv_symm_epsilon_ne_one
  exact ⟨GlueBE.eps l, u, by rw [GlueBE.eps_μ]; exact e⟩

theorem tFil : TFil l := fun A n =>
  (eps_tA l).elim fun ε h => h.elim fun u hu => by
    rw [hu, map_mul]
    exact Ideal.mul_mem_right _ _ (ε.μ_mem false A n)

end CrystallineSemistableComparison.HT
