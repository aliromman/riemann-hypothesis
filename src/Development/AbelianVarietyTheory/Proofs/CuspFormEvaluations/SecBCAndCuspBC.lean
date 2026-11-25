module

public import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.SectionBaseChangeOfBasis
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

namespace GlobalTheory.FieldBC

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem secBC_and_cuspBC (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) :
    SecBC Xo hle ∧ ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), CuspBC hle U :=
  ⟨GlobalTheory.SecFieldChange.secBC_holds hle, fun _ U => GlobalTheory.SecFieldChange.cuspBC_holds hle U⟩

end GlobalTheory.FieldBC
