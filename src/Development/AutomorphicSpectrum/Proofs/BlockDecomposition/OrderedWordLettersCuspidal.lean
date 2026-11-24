module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
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

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace GlobalTheory.CompanionTheory.ZcWords

theorem wtW_isCusp {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {h : ℕ} (Δ : Fin h → Segment k) :
    ∀ c ∈ wtW Δ, c.IsCusp := by
  intro c hc
  obtain ⟨l, hl, hcl⟩ := List.mem_flatten.1 hc
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hl
  obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hcl
  exact Segment.isCusp_term _ _

end GlobalTheory.CompanionTheory.ZcWords
