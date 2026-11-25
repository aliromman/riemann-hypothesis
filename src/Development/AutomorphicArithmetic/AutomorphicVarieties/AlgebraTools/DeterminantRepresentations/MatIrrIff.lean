module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BaseRepGL3NormalisedOfPsiEqOne
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IrrIffSpan
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg

@[expose] public section

open Polynomial Matrix UpperTheory.V UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.matIrrIff :
    ∀ {K G : Type} [Field K] [IsAlgClosed K] [Group G] {n : ℕ} (H : Subgroup G) (ρ : G →* Matrix (Fin n) (Fin n) K),
    U3.MatIrr H ρ ↔ Submodule.span K (Set.range fun h : H => ρ h) = ⊤ := by
  intro K G _ _ _ n H ρ
  have h := _root_.UpperTheory.Reformulated.B.Qe4.irrIffSpan (K := K) (ρ.comp H.subtype)
  refine Iff.trans ?_ h
  constructor
  · intro h1 N hN; exact h1 N fun g hg v hv => hN ⟨g, hg⟩ v hv
  · intro h1 N hN; exact h1 N fun g v hv => hN g g.2 v hv
