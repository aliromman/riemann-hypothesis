module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtSide
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace CrystallineSemistableComparison.AdicGeo

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

abbrev str (M : Model l K) : GlobalTheory.Et.geom (PadicAlgCl l) M.q ⟶ Spec (CommRingCat.of (PadicAlgCl l)) :=
  pullback.snd M.q (Spec.map (CommRingCat.ofHom (algebraMap K (PadicAlgCl l))))

theorem proper_p {M : Model l K} (h : M.Good) : IsProper M.p := by
  obtain ⟨N, i, hi, e⟩ := h.1
  have := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str (OK l K) N
  rw [← e]
  infer_instance

end CrystallineSemistableComparison.AdicGeo
