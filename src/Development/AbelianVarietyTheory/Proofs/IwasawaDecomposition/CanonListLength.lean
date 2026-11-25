module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
public import Formalism.PadicSubsetSums.CentralIdempotents.GaloisConjCentralIdempotent
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

namespace GlobalTheory.SerCmp

open Formalism.IrreducibleCountingLemmas.TYPES

def canonList {g : ℕ} [Fact g.Prime] {r s : ℕ} (b : Fin r → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} (ZMod g))) : List (GlobalTheory.GLq.Pc g) :=
  (List.finRange s).map fun c =>
    ⟨Fintype.card {i // b i = c}, fun x => (transp (Fintype.equivFin {i // b i = c}) (lam c)).character x⟩

theorem canonList_length {g : ℕ} [Fact g.Prime] {r s : ℕ} (b : Fin r → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} (ZMod g))) : (canonList b lam).length = s := by
  simp [canonList]

end GlobalTheory.SerCmp
