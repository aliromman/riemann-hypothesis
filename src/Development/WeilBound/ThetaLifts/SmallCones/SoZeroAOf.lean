module

public import Development.WeilBound.ThetaLifts.CTKernel
public import Development.WeilBound.ThetaLifts.SmallCones.SoDefs
public import Development.WeilBound.ThetaLifts.SmallCones.FormSwapZero
public import Development.WeilBound.ThetaLifts.SmallCones.LinExOf
public import Development.WeilBound.ThetaLifts.SmallCones.SoZero
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

namespace PositivityTheory.ThKCT

theorem soEv_of' (hLow : Low) : SoEv := soEv_of linEx_of hLow

theorem soZeroA'_of' (hX : PositivityTheory.ThKG.MixX) (hE : ThetaExp) (hU : EvUniq) : SoZeroA' := soZeroA'_of linEx_of hX hE hU

end PositivityTheory.ThKCT
