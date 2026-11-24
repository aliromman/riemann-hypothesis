module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
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

open NumberField IsDedekindDomain GlobalTheory.LocDict

namespace GlobalTheory.LTRecip

instance charZero_adicCompletion (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective

instance isSepClosure_kbar (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    IsSepClosure (w.adicCompletion E) (Kbar w) := inferInstance

end GlobalTheory.LTRecip

end
