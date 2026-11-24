module

public import ReciprocityTheory.Automorphisms.Unitary
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

open NumberField IsDedekindDomain ReciprocityTheory.Aut

namespace GlobalTheory.TypeTame

noncomputable abbrev conjSP {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) : SplitPlace L :=
  ⟨s.v, s.i.comp (IsCMField.complexConj L).toAlgHom⟩

theorem conjSP_i {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (x : L) :
    (conjSP s).i x = s.i (IsCMField.complexConj L x) := rfl

end GlobalTheory.TypeTame
