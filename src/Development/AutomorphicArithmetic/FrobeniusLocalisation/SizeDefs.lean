module

public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
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

namespace UpperTheory.HF.Formalism.HC

open UpperTheory.HF _root_.Formalism _root_.Formalism.HC

namespace Frame

open _root_.Formalism.HC.Frame

variable (φ : Frame)

end Frame

namespace HostRaw

open _root_.Formalism.HC.HostRaw

variable {φ : Frame} (H : HostRaw φ)

def frobG (p : ℕ) : φ.GG :=
  if h : Nat.Coprime p H.condN then H.art (ZMod.unitOfCoprime p h) else 1

def Inert (p : ℕ) : Prop := p.Prime ∧ jacobiSym (-(H.d : ℤ)) p = -1

theorem frobG_of_coprime {p : ℕ} (h : Nat.Coprime p H.condN) : H.frobG p = H.art (ZMod.unitOfCoprime p h) := dif_pos h

end HostRaw

end UpperTheory.HF.Formalism.HC

end
