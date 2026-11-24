module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ThetaSetupAlgebraMaps
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

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace CrystallineSemistableComparison

def ComparisonPairing : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (R : Per l K) (G : Model l K → Prop)
  (D : Dat R), R.Facts → EtSide G → D.Laws G → EMap G D → BMap G D → PMap G D →
    ∃ P : Pre G R, ∀ (G' : Model l K → Prop) (S : Subring R.B), (R.tB)⁻¹ ∈ S → (∀ z, R.q z ∈ S) → D.Span G' S →
      ∀ M, G M → G' M → ∀ n, P.Span M n S

def ComparisonInjectiveStrict : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (R : Per l K) (G : Model l K → Prop)
  (P : Pre G R), R.Facts → EtSide G → ∀ M, G M → ∀ n, P.Inj M n ∧ P.Strict M n

def ComparisonAdmissible : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (R : Per l K) (G : Model l K → Prop)
  (P : Pre G R) (S : Subring R.B), R.Reg S → ∀ M, G M → ∀ n, P.Inj M n → P.Span M n S →
    ∀ (a : ℕ) (b : Module.Basis (Fin a) ℚ_[l] (M.V n)), R.admitted S (M.mat n b)

end CrystallineSemistableComparison
