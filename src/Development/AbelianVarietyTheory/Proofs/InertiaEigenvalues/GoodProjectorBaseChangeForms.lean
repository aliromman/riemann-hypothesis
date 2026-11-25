module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Objects
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

open Formalism.BasicNotions Formalism.IndefR.NX
open scoped TensorProduct

namespace GlobalTheory.GoodSS

variable {D : D7} (S : RatDat D.ntw)

def opK (j : ℕ) (f : Module.End D.what₂.LL (S.WL j)) (hf : ∀ x ∈ (S.A j).WK, f x ∈ (S.A j).WK) :
    Module.End S.Ks (FmK S j) :=
  (f.restrictScalars S.Ks).restrict (p := (S.A j).WK) (q := (S.A j).WK) hf

def goodProjectorBaseChangeForms (j : ℕ) (hst : RhoStab S j) (hχ : ChiInLL0 S j) (eC : G0g D.nd → ↥D.LL0) :
    Module.End ↥D.LL0 (↥D.LL0 ⊗[S.Ks] FmK S j) :=
  ∑ᶠ g : G0g D.nd, (eC g * (chiL S j hχ (S.eG.symm g))⁻¹) •
    LinearMap.baseChange ↥D.LL0 (rhoKG S j hst (S.eG.symm g))

end GlobalTheory.GoodSS
