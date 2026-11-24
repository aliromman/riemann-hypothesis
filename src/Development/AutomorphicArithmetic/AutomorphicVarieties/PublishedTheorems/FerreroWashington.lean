module

public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.RingTheory.ClassGroup.Basic
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

open NumberField

namespace UpperTheory.V.Published

def FerreroWashington : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [NumberField K] [IsAbelianGalois ℚ K],
    (∃ ζ : K, IsPrimitiveRoot ζ (if l = 2 then 4 else l)) →
    ∃ r : ℕ, ∀ (n : ℕ) (K' : Type) [Field K'] [NumberField K'] [Algebra K K'] [IsCyclotomicExtension {l ^ n} K K'],
      Nat.card (ClassGroup (𝓞 K') ⧸ (powMonoidHom l : ClassGroup (𝓞 K') →* ClassGroup (𝓞 K')).range) ≤ l ^ r

end UpperTheory.V.Published
