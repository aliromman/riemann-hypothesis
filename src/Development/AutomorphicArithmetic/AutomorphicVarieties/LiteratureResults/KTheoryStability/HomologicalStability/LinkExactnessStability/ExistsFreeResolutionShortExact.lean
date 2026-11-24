module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.CategoryTheory.Abelian.Exact
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
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PermRepSingle

@[expose] public section

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab

theorem exists_free_shortExact : ∀ (k G : Type) [CommRing k] [Group G] (A : Rep k G), ∃ (ι : Type) (K : Rep k G) (i : K ⟶ Rep.free k G ι) (e : Rep.free k G ι ⟶ A) (h : i ≫ e = 0), (ShortComplex.mk i e h).ShortExact := by
  intro k G _ _ A
  let e : Rep.free k G A ⟶ A := Rep.freeLift k G A (fun x => x)
  have he : Epi e := (Rep.epi_iff_surjective e).2 fun x =>
    ⟨Finsupp.single x (MonoidAlgebra.single 1 1), by
      simp [e, Representation.freeLift_single_single]⟩
  exact ⟨A, kernel e, kernel.ι e, e, kernel.condition e,
    ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel e) inferInstance he⟩

end GlobalTheory.HomStab

