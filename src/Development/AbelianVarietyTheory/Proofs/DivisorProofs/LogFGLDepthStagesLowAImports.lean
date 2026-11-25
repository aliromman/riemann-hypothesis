module

public import Mathlib.LinearAlgebra.Matrix.Defs
public import ReciprocityTheory.DualLattices.VEqZeroOfPowEqOne
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtOrderProdSub

@[expose] public section

namespace GlobalTheory.DepthStages

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh

noncomputable section

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}

def rebase (G : LogFGL v d) (X : Matrix (Fin d) (Fin d) C) (γ : Fin d → Fin d → PowerSeries C) :
    Fin d → Fin d → PowerSeries C :=
  fun a => G.sumF fun b => rescaleCurve (X a b) (γ b)

def glue {ι : Type} (lab : Fin d → ι) (S : ι → Finset (Fin d)) (x : ι → Matrix (Fin d) (Fin d) C) :
    Matrix (Fin d) (Fin d) C :=
  Matrix.of fun a b => if a ∈ S (lab a) then x (lab a) a b else if a = b then 1 else 0

end

end GlobalTheory.DepthStages
