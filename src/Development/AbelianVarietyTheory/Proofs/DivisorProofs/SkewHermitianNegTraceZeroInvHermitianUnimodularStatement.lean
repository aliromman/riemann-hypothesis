module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramHspOf
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianNegTraceZeroInvHermitianUnimodular
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)


theorem _root_.GlobalTheory.T.skewHermitian_neg_traceZero_inv_hermitian_unimodular : ∀ (D : D7) (B : Base D.host.F D.host.E), B.IsGood D.sp.cm.sig →
    ∀ (d : ℕ) (Y : Spc D.host.F D.host.E d) (r s : ℕ), Y.IsSkew D.sp.cm.sig B r s →
      IsUnit Y.J.det ∧ ∃ L : Submodule (𝓞 D.host.E) (Fin d → D.host.E), L.IsLattice D.host.E ∧
        (GlobalTheory.WeilSchrodinger.sesq D (-D.host.xi0 • Y.J⁻¹)).IsSymm ∧
        (GlobalTheory.WeilSchrodinger.sesq D (-D.host.xi0 • Y.J⁻¹)).Nondegenerate ∧
        Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.WeilSchrodinger.sesq D (-D.host.xi0 • Y.J⁻¹)) L := by
  first | exact @GlobalTheory.WeilSchrodingerSkew.main
