module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassPairingClassBounds
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

namespace GlobalTheory

theorem localMass_le_genericMass_nine : ∀ k r : ℕ, 4 * r + 7 ≤ k → Formalism.L2.SG.FamDefs.LocalLowerBoundAllCosets k r 9 := by
  intro k r hk F _ _ _ E _ _ _ _ M hM V _ _ H hV P hP R d0 h0 d t ht Y0 hZ
  exact GlobalTheory.mass_pairingClass_bounds M hM H r k P hk hV hP R d0 h0 d t ht Y0 _ rfl hZ _ rfl

end GlobalTheory
