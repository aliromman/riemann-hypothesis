module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.HasPairingOfHerm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CuspidalFiniteness.ExistsZalgOfCenterU
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.IsHermOfInner
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

open NumberField GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af


open GroundTheory.Automorphic in
theorem UpperTheory.V.Br.hermEx : Gk.HermEx :=
  Gk.hermEx_of (fun _ _ _ _ _ => CuspFin.mem_cuspForms_of) fun F _ _ _ a => by
    refine ⟨(Fb.lieEq F a).toLinearMap, Subtype.ext ?_, fun X φ _ => congrArg Subtype.val (CuspFin.uAction_lieEq X φ)⟩
    rw [UnitaryAdmissible.coe_centralZ, Algebra.algebraMap_eq_smul_one, ← Fb.lieEq_oneL]
    rfl
