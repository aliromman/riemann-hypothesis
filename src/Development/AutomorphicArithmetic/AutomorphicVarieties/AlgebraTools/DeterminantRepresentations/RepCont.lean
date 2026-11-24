module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
public import Mathlib.Topology.Instances.Matrix
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.RepApi
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
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
public import Mathlib.Topology.Algebra.MvPolynomial

@[expose] public section

open Polynomial UpperTheory.V.W

private theorem UpperTheory.V.AlgebraTools.Det.cont_charpoly_coeff {n : ℕ} {K : Type} [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] (i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by
  have h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))

theorem UpperTheory.V.AlgebraTools.Det.repCont :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace G] (ρ : G →* Matrix (Fin n) (Fin n) A),
    Continuous ρ → ∀ i, Continuous fun g : G => (GDet.ofRep ρ).lam i (MonoidAlgebra.single g 1) := by
  intro n A G _ _ _ _ _ ρ hρ i
  have h : (fun g : G => (GDet.ofRep ρ).lam i (MonoidAlgebra.single g 1))
      = fun g => (-1) ^ i * (ρ g).charpoly.coeff (n - i) := by
    funext g
    rw [GDet.lam, (UpperTheory.V.AlgebraTools.Det.repApi ρ).2.1]
  rw [h]
  exact continuous_const.mul ((UpperTheory.V.AlgebraTools.Det.cont_charpoly_coeff (n - i)).comp hρ)
