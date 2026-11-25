module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtalePrimitiveRootsExistLocally : Prop :=
  ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), (IsUnit (q : Γ(U, ⊤)) → Loc U fun V _ => Nonempty (Prim q Γ(V, ⊤))) ∧ (∀ ζ ξ : Prim q Γ(U, ⊤), Loc U fun _ g => ∃ a : (ZMod q)ˣ, g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val) ∧ (∀ (ζ : Prim q Γ(U, ⊤)) (x : Γ(U, ⊤)), x ^ q = 1 → Loc U fun _ g => ∃ a : ℕ, g.appTop.hom x = g.appTop.hom ζ.1 ^ a) ∧ (IsUnit (q : Γ(U, ⊤)) → ∀ u : (Γ(U, ⊤))ˣ, Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u)
