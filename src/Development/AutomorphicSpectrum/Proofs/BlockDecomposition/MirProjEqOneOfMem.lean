module

import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCellStructureData
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.ColMatMulGlEmbMat
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
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto

@[expose] public section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

namespace GlobalTheory.CompanionTheory.BZMirAdj

section Alg

variable (k : Type) [Field k]

theorem mirProj_levi (n : ℕ) (g : GL (Fin n) k) : mirabolicProjection k n (levi k n g) = g := by
  apply Units.ext
  ext i j
  change GlobalTheory.BZMir.blockMat k n (GlobalTheory.BZMir.glEmbMat k n (g : Matrix (Fin n) (Fin n) k)) i j =
    (g : Matrix (Fin n) (Fin n) k) i j
  simp [GlobalTheory.BZMir.blockMat, GlobalTheory.BZMir.glEmbMat]

theorem mirProj_eq_one_of_mem (n : ℕ) (u : Mir k n) (hu : u ∈ MirUin k n) : mirabolicProjection k n u = 1 := by
  rw [GlobalTheory.BZMir.MirUin, Subgroup.mem_subgroupOf, GlobalTheory.BZMir.MirU,
    MonoidHom.mem_range] at hu
  obtain ⟨v, hv⟩ := hu
  apply Units.ext
  ext i j
  change GlobalTheory.BZMir.blockMat k n ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j =
    (1 : Matrix (Fin n) (Fin n) k) i j
  rw [GlobalTheory.BZMir.blockMat, ← hv]
  change ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) +
    GlobalTheory.BZMir.colMat k n (Multiplicative.toAdd v)) (Fin.castSucc i) (Fin.castSucc j) =
    (1 : Matrix (Fin n) (Fin n) k) i j
  simp [GlobalTheory.BZMir.colMat, Matrix.one_apply, Fin.castSucc_ne_last]

theorem mem_of_mirProj_eq_one (n : ℕ) (y : Mir k n) (hy : mirabolicProjection k n y = 1) : y ∈ MirUin k n := by
  apply GlobalTheory.CompanionTheory.BZPhiPG.Grp.mem_of_mirProj_eq_one' <;> assumption

end Alg

section Rep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Rep

end GlobalTheory.CompanionTheory.BZMirAdj
