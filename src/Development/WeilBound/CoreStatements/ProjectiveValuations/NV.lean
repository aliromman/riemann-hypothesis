module

public import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
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

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace DifferentiableLines

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

def NV (Xo : Moduli D l) (c : Coeff l) (σ : c.F →+* ℂ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ y : FrPt Xo c (CAt σ), ∃ (a' : (E →+* ℂ) × ℕ → ℕ) (n' : ℕ), Dom a' n' ∧ ∃ g ∈ sec Xo c a' n',
    ∃ f ∈ sec Xo c (a + a') (n + n'), evR Xo c g y ≠ 0 ∧ evR Xo c f y ≠ 0

end DifferentiableLines
