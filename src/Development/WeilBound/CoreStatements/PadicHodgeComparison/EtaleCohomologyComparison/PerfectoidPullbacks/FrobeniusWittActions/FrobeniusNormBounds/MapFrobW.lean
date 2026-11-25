module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.IsUnitWitt
import Mathlib.Tactic.Linter.Style
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

open GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison.Pb.G3

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem map_frob_w (r : Res l K) (w : WittVector l r.k) :
    WittVector.map r.s (WittVector.frobenius w) = WittVector.frobenius (WittVector.map r.s w) := by
  rw [WittVector.frobenius_eq_map_frobenius, WittVector.frobenius_eq_map_frobenius]
  ext n
  simp only [WittVector.map_coeff, frobenius_def, map_pow]

theorem w_phi (r : Res l K) (w : WittVector l r.k) :
    ACris.phi (K := ℂ_[l]) (p := l) (r.w w) = r.w (WittVector.frobenius w) := by
  show ACris.phi (K := ℂ_[l]) (p := l)
    (algebraMap (Ainf l) (Acris l) (WittVector.map r.s w)) =
    algebraMap (Ainf l) (Acris l) (WittVector.map r.s (WittVector.frobenius w))
  rw [ACris.phi_algebraMap, map_frob_w]
  rfl

end CrystallineSemistableComparison.Pb.G3
