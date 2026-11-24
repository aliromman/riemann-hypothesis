module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
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

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace PositivityTheory.HtPt.Kftwo

structure PairHost {E E' : Type} [Field E] [NumberField E] [IsCMField E] [Field E'] [NumberField E'] [IsCMField E']
    (H : Host E) (H' : Host E') where

  ψ : 𝓞 E' →+* Matrix (Fin 2) (Fin 2) (𝓞 E)

  σ : 𝓞 E' ≃+* 𝓞 E'
  bar : ∀ a i j, ψ (H'.bar a) i j = H.bar (ψ a j i)
  w0 : ψ H'.w0 = Matrix.scalar (Fin 2) H.w0
  conj : ∀ a, ψ (σ a) * Matrix.diagonal ![1, -1] = Matrix.diagonal ![1, -1] * ψ a
  rt : σ H'.rt = H'.rt
  chars : ∀ (k : Type) [Field k] [CharZero k] (τ τ' : 𝓞 E' →+* k), τ H'.rt = τ' H'.rt →
    τ' = τ ∨ τ' = τ.comp σ.toRingHom

end PositivityTheory.HtPt.Kftwo
