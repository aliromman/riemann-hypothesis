module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
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
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn

@[expose] public section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi

theorem continuous_glEmbMat_comp {k X : Type} [Field k] [TopologicalSpace k] [TopologicalSpace X] (m : ℕ)
    {f : X → Matrix (Fin m) (Fin m) k} (hf : Continuous f) :
    Continuous fun x => glEmbMat k m (f x) := by
  refine continuous_matrix fun i j => ?_
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp only [GlobalTheory.BZMir.glEmbMat, Fin.lastCases_last, Fin.lastCases_castSucc] <;>
    first
    | exact continuous_const
    | exact hf.matrix_elem _ _

theorem continuous_iotaM : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), Continuous (embedding₂ k n) := by
  intro k _ _ _ _ n
  have hemb : Continuous (GlobalTheory.BZMir.glEmb k (n + 1)) :=
    Continuous.units_map _ (GlobalTheory.CompanionTheory.LeibPhi.continuous_glEmbMat_comp (n + 1) continuous_id)
  exact continuous_induced_rng.2 (hemb.comp continuous_subtype_val)

end GlobalTheory.CompanionTheory.LeibPhi

end
