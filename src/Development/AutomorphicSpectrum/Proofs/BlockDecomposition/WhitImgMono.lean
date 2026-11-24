module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhitKerLeComapMap
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

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.BZNuPair

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {X : Type} [AddCommGroup X] [Module ℂ X]

def whitImg (ψ : AddChar k Circle) (d : Fin 2 → ℕ) (J : Representation ℂ (Levi k fun a => Fin (d a)) X)
    (T : Subrepresentation J) : Subrepresentation (whit2 ψ d J) :=
  ⟨T.toSubmodule.map (whitKer ψ d J).mkQ, fun g v hv => by
    obtain ⟨t, ht, rfl⟩ := hv
    exact ⟨J (firstEmb d g) t, T.apply_mem_toSubmodule _ ht, rfl⟩⟩

theorem whitImg_mono (ψ : AddChar k Circle) (d : Fin 2 → ℕ) (J : Representation ℂ (Levi k fun a => Fin (d a)) X)
    {T T' : Subrepresentation J} (h : T' ≤ T) : whitImg ψ d J T' ≤ whitImg ψ d J T :=
  Submodule.map_mono (f := (whitKer ψ d J).mkQ) h

end

end GlobalTheory.CompanionTheory.BZNuPair

end
