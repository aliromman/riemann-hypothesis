import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne
import Lean.Meta.Instances

open Lean Meta IsLocalRing UpperTheory.V.Pr

run_meta do
  let name := ``IsCD.toIsDiscreteValuationRing
  let some entry := (Meta.instanceExtension.getState (← getEnv)).instanceNames.find? name
    | throwError "missing DVR instance"
  let args ← forallTelescope (← getConstInfo name).type fun xs _ =>
    entry.synthOrder.mapM fun i => do
      let binder ← xs[i]!.fvarId!.getDecl
      pure (binder.userName, (← inferType xs[i]!).getAppFn.constName?)
  logInfo m!"{name}: {args}"

section
variable (O A : Type) [CommRing O] [CommRing A] [Algebra O A]

example [IsCD O A] : IsDomain A := inferInstance
example [IsCD O A] : IsDiscreteValuationRing A := inferInstance

example [IsDomain A] [IsDiscreteValuationRing A] :
    IsCD O A ↔ IsAdicComplete (maximalIdeal A) A ∧
      IsLocalHom (algebraMap O A) ∧ Finite (ResidueField A) := by
  constructor
  · intro h
    exact ⟨h.complete, h.isLocalHom, h.fin⟩
  · rintro ⟨hc, hl, hf⟩
    exact { complete := hc, isLocalHom := hl, fin := hf }
end
