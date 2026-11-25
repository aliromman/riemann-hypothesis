module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.CentralizerReps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantAddChar
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.BaseOrbits
public import GroundTheory.AutomorphicForms.ContragredientTranspose.GelfandKazhdan
public import GroundTheory.AutomorphicForms.GL2.GJFELevi
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.ModulusBounds
public import GroundTheory.AutomorphicForms.WhittakerOrbit
public import Mathlib.GroupTheory.CosetCover
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Fourier, Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.ModulusInduction

-- ===== clump member: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Fourier =====
-- clump-header: {"m": "Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Fourier", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantAddChar\npublic import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField\npublic import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.BaseOrbits\npublic import GroundTheory.AutomorphicForms.ContragredientTranspose.GelfandKazhdan\npublic import GroundTheory.AutomorphicForms.GL2.GJFELevi\nimport GroundTheory.AutomorphicForms.MeasuresModulus\n\n"}
section -- clump:auto
@[expose] public section
noncomputable section
set_option linter.unusedSectionVars false

section
open Matrix MeasureTheory GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil Set

namespace PositivityTheory.RgUd.T.Nil.Four

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil

section Top

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def PhiP : Prop :=
  ∀ (n : ℕ) (Z : SubM k n), CR Z →
    ∃ Φ Φ' : (Sp k n → ℂ) →ₗ[ℂ] (Sp k n → ℂ),
      (∀ f ∈ SuppUniv k n, Φ f ∈ SuppUniv k n) ∧
      (∀ f ∈ SuppUniv k n, Φ' f ∈ SuppUniv k n) ∧
      (∀ f ∈ SuppUniv k n, ∀ y, (∀ p ∈ Fib Z y, f p = 0) → ∀ p ∈ Fib Z y, Φ f p = 0) ∧
      (∀ g ∈ Gz Z, ∀ f ∈ SuppUniv k n, ∀ p ∈ Bz Z ×ˢ univ, Φ (fun q => f (act g q)) p = Φ f (act g p)) ∧
      (∀ f ∈ supportedIn (UU : Set (Sp k n)), Φ f ∈ supportedIn (UU : Set (Sp k n))) ∧
      (∀ f ∈ supportedIn (UU : Set (Sp k n)), Φ' f ∈ supportedIn (UU : Set (Sp k n))) ∧
      (∀ f ∈ SuppUniv k n, ∀ p ∈ Bz Z ×ˢ univ, Φ (Φ' f) p = f p) ∧
      (∀ (t : kˣ), ∀ f ∈ SuppUniv k n, ∀ p ∈ Bz Z ×ˢ univ,
        Φ f (sig Z t p) = ((((nabs k t)⁻¹ ^ dB0 Z : ℝ)) : ℂ) * Φ (fun q => f (sig Z t⁻¹ q)) p)

def CompP : Prop :=
  ∀ (n : ℕ) (Z : SubM k n), CR Z →
    (∀ (t : kˣ), ∀ f ∈ SuppUniv k n, (fun q => f (sig Z t q)) ∈ SuppUniv k n) ∧
    (∀ (g : GLn k n), ∀ f ∈ SuppUniv k n, (fun q => f (act g q)) ∈ SuppUniv k n) ∧
    (∀ (t : kˣ) p, p ∈ Bz Z ×ˢ univ → sig Z t p ∈ Bz Z ×ˢ univ) ∧
    (∀ g ∈ Gz Z, ∀ p, p ∈ Bz Z ×ˢ univ → act g p ∈ Bz Z ×ˢ univ)

theorem isClosed_Bz (Z : SubM k n) : IsClosed (Bz Z) := isClosed_Bz_shared Z

theorem locQ_pf : LocQ (k := k) := by
  intro n Z hCR hfib ξ hsupp hinv f hf
  have : TotallyDisconnectedSpace k := totallyDisconnectedSpace_localField
  have : TotallyDisconnectedSpace (Mat k n) := Pi.totallyDisconnectedSpace
  let qf : Sp k n → Fin (Module.finrank k Z) → k := fun q => qZ Z q.1
  let W : Submodule ℂ (Sp k n → ℂ) :=
    { carrier := {w | ∀ V, IsClopen V → ξ (fun x => (qf ⁻¹' V).indicator 1 x * w x) = 0}
      add_mem' := fun {a b} ha hb V hV => by
        rw [show (fun x => (qf ⁻¹' V).indicator 1 x * (a + b) x) =
            (fun x => (qf ⁻¹' V).indicator 1 x * a x) + fun x => (qf ⁻¹' V).indicator 1 x * b x by
          funext x; simp [mul_add], map_add, ha V hV, hb V hV, add_zero]
      zero_mem' := fun _ _ => by simp only [Pi.zero_apply, mul_zero]; exact map_zero ξ
      smul_mem' := fun c a ha V hV => by
        rw [show (fun x => (qf ⁻¹' V).indicator 1 x * (c • a) x) =
            c • fun x => (qf ⁻¹' V).indicator 1 x * a x by funext x; simp; ring, map_smul, ha V hV, smul_zero] }
  have hp : Continuous qf := (continuous_qZ_s Z).comp continuous_fst
  have h1 : SuppUniv k n ⊓ vanishingOn (Bz Z ×ˢ (univ : Set (Fin n → k))) ≤ W := fun w hw V hV =>
    hsupp _ (indicator_mul_mem (hV.preimage hp) (Submodule.mem_inf.mp hw).1) fun x hx => by
      simp [(Submodule.mem_inf.mp hw).2 x hx]
  have h2 : ∀ V, IsClopen V → ∀ w ∈ W, (fun x => (qf ⁻¹' V).indicator 1 x * w x) ∈ W := fun V hV w hw V' hV' => by
    convert hw (V ∩ V') (hV.inter hV') using 2
    funext x; by_cases ha : qf x ∈ V <;> by_cases hb : qf x ∈ V' <;> simp [indicator, ha, hb]
  have hfW : f ∈ W := mem_of_forall_fiber ((isClosed_Bz Z).prod isClosed_univ) hp h1 h2
    ⟨hf.1, subset_univ _⟩ fun y => by_contra fun hny => by
      obtain ⟨l, hlf, hlM⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hny inferInstance
      have hl0 : ∀ m ∈ W ⊔ SuppUniv k n ⊓ vanishingOn (Bz Z ×ˢ univ ∩ qf ⁻¹' {y}), l m = 0 := fun m hm => by
        have := Submodule.mem_map_of_mem (f := l) hm; rw [hlM] at this; simpa using this
      exact hlf (hfib y l
        (fun g hg hgv => hl0 _ (Submodule.mem_sup_right (Submodule.mem_inf.2 ⟨hg, fun x hx =>
          hgv x ⟨⟨hx.1.1, hx.2⟩, trivial⟩⟩)))
        (fun g hg h hh => sub_eq_zero.mp (map_sub l _ _ ▸ hl0 _ (Submodule.mem_sup_left fun V hV => by
          have e : (fun x => (qf ⁻¹' V).indicator 1 x * ((fun q => h (act g q)) - h) x) =
              (fun q => (fun x => (qf ⁻¹' V).indicator 1 x * h x) (act g q)) -
                fun x => (qf ⁻¹' V).indicator 1 x * h x := by
            funext x; have hpx : qf (act g x) = qf x := PositivityTheory.RgUd.T.Nil.qZ_conj_s Z hg x.1
            by_cases ha : qf x ∈ V <;> simp [indicator, ha, hpx]
          rw [e, map_sub, hinv g hg _ (indicator_mul_mem (hV.preimage hp) hh), sub_self]))) f hf)
  simpa using hfW univ isClopen_univ

end Top

namespace Alg
variable {k : Type} [Field k] {n : ℕ}
theorem trB_nondeg [CharZero k] {Z : SubM k n} (hZ : CR Z)
    {w : Mat k n} (hw : w ∈ Bz Z) (h : ∀ b ∈ Bz Z, trace (b * w) = 0) : w = 0 :=
  Desc.UniPf.nondeg Z hZ w ((Subalgebra.mem_centralizer_iff k).2 hw) fun y hy => by
    rw [trace_mul_comm]; exact h y ((Subalgebra.mem_centralizer_iff k).1 hy)
end Alg

namespace Phi2

section AlgPhi2
variable {k : Type} [Field k] {n : ℕ} (Z : SubM k n)

def qL : Mat k n →ₗ[k] (Fin (Module.finrank k Z) → k) where
  toFun := qZ Z
  map_add' x y := by funext i; simp [qZ, mul_add]
  map_smul' c x := by funext i; simp [qZ]

def BzL : Submodule k (Mat k n) where
  carrier := Bz Z
  add_mem' {a b} ha hb z hz := by rw [mul_add, add_mul, ha z hz, hb z hz]
  zero_mem' _ _ := by simp
  smul_mem' _ _ hx z hz := by rw [mul_smul_comm, smul_mul_assoc, hx z hz]

def B0 : Submodule k (Mat k n) := BzL Z ⊓ LinearMap.ker (qL Z)
abbrev d : ℕ := Module.finrank k (B0 Z)
def bas : Module.Basis (Fin (d Z)) k (B0 Z) := Module.finBasis k (B0 Z)
def ee (j : Fin (d Z)) : Mat k n := (bas Z j : B0 Z)
def E (u : Fin (d Z) → k) : Mat k n := ((bas Z).equivFun.symm u : B0 Z)
def D (x : Mat k n) : Fin (d Z) → k := fun j => trace (ee Z j * x)
def G : Matrix (Fin (d Z)) (Fin (d Z)) k := Matrix.of fun i j => trace (ee Z i * ee Z j)

theorem E_apply (u : Fin (d Z) → k) : E Z u = ∑ j, u j • ee Z j := by simp [E, ee, Module.Basis.equivFun_symm_apply]
theorem E_mem (u : Fin (d Z) → k) : E Z u ∈ B0 Z := ((bas Z).equivFun.symm u).2
theorem E_add (u u' : Fin (d Z) → k) : E Z (u + u') = E Z u + E Z u' := by simp [E, add_smul, Finset.sum_add_distrib]
theorem E_smul (c : k) (u : Fin (d Z) → k) : E Z (c • u) = c • E Z u := by simp only [E, map_smul, Submodule.coe_smul]
theorem E_neg (u : Fin (d Z) → k) : E Z (-u) = -E Z u := by simp [E]
theorem E_injective : Function.Injective (E Z) := fun _ _ h => (bas Z).equivFun.symm.injective (Subtype.ext h)
theorem exists_E {w : Mat k n} (hw : w ∈ B0 Z) : ∃ u, E Z u = w := ⟨(bas Z).equivFun ⟨w, hw⟩, by simp [E]⟩
theorem dot_D (u : Fin (d Z) → k) (x : Mat k n) : u ⬝ᵥ D Z x = trace (E Z u * x) := by
  rw [E_apply, Finset.sum_mul, trace_sum]; simp [dotProduct, D, trace_smul]
theorem D_E (u : Fin (d Z) → k) : D Z (E Z u) = G Z *ᵥ u := by
  funext i; simp [D, G, E_apply, mulVec, dotProduct, Finset.mul_sum, trace_sum, trace_smul, mul_comm]
theorem D_add (x y : Mat k n) : D Z (x + y) = D Z x + D Z y := by funext j; simp [D, mul_add]
theorem D_sub (x y : Mat k n) : D Z (x - y) = D Z x - D Z y := by funext j; simp [D, mul_sub]
theorem D_smul (c : k) (x : Mat k n) : D Z (c • x) = c • D Z x := by funext j; simp [D]
theorem G_symm : (G Z)ᵀ = G Z := by ext i j; exact Matrix.trace_mul_comm (ee Z j) (ee Z i)

def Dl : Mat k n →ₗ[k] (Fin (d Z) → k) where
  toFun := D Z
  map_add' := D_add Z
  map_smul' := D_smul Z

private theorem orth {z w : Mat k n} (hz : z ∈ Z) (hw : w ∈ B0 Z) : trace (z * w) = 0 := by
  have hq : qZ Z w = 0 := LinearMap.mem_ker.mp (Submodule.mem_inf.mp hw).2
  have hz' := congrArg Subtype.val ((Module.finBasis k Z).sum_repr ⟨z, hz⟩)
  simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at hz'
  rw [← hz', Finset.sum_mul, trace_sum]
  exact Finset.sum_eq_zero fun i _ => by
    rw [smul_mul_assoc, trace_smul, show trace (((Module.finBasis k Z) i : Mat k n) * w) = 0 by
      simpa [qZ] using congrFun hq i, smul_zero]

private theorem D_Z {z : Mat k n} (hz : z ∈ Z) : D Z z = 0 := by
  funext j; simp only [D, Pi.zero_apply]; rw [trace_mul_comm]; exact orth Z hz (bas Z j).2

theorem Z_le_Bz (hZ : CR Z) {z : Mat k n} (hz : z ∈ Z) : z ∈ Bz Z := fun a ha => hZ.1 a ha z hz

structure Hyp : Prop where
  pi_mem : ∀ x, piZ Z x ∈ Z
  q_pi : ∀ x, qZ Z (piZ Z x) = qZ Z x
  pi_eq : ∀ x c, c ∈ Z → qZ Z c = qZ Z x → piZ Z x = c
  trB : ∀ w ∈ Bz Z, (∀ b ∈ Bz Z, trace (b * w) = 0) → w = 0

def Pr (x : Mat k n) : Mat k n := E Z ((G Z)⁻¹ *ᵥ D Z x)

variable {Z}

private theorem sub_pi_mem (hZ : CR Z) (h : Hyp Z) {b : Mat k n} (hb : b ∈ Bz Z) : b - piZ Z b ∈ B0 Z :=
  ⟨(BzL Z).sub_mem hb (Z_le_Bz Z hZ (h.pi_mem b)), by
    show qZ Z (b - piZ Z b) = 0; funext i; simp only [qZ, mul_sub, trace_sub, Pi.zero_apply]
    exact sub_eq_zero.2 (congrFun (h.q_pi b) i).symm⟩

theorem G_inj (hZ : CR Z) (h : Hyp Z) {u : Fin (d Z) → k} (hu : G Z *ᵥ u = 0) : u = 0 := by
  have hD : D Z (E Z u) = 0 := by rw [D_E, hu]
  have h0 : E Z u = 0 := h.trB _ (E_mem Z u).1 fun b hb => by
    obtain ⟨v, hv⟩ := exists_E Z (sub_pi_mem hZ h hb)
    rw [← sub_add_cancel b (piZ Z b), add_mul, trace_add, ← hv, ← dot_D, hD, dotProduct_zero,
      orth Z (h.pi_mem b) (E_mem Z u), add_zero]
  exact E_injective Z (by rw [h0]; simp [E])

theorem G_det (hZ : CR Z) (h : Hyp Z) : (G Z).det ≠ 0 := fun h0 => by
  obtain ⟨u, hu0, hu⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0; exact hu0 (G_inj hZ h hu)

theorem D_Pr (hZ : CR Z) (h : Hyp Z) (x : Mat k n) : D Z (Pr Z x) = D Z x := by
  rw [Pr, D_E, mulVec_mulVec, mul_nonsing_inv _ (Ne.isUnit (G_det hZ h)), one_mulVec]

theorem Pr_E (hZ : CR Z) (h : Hyp Z) (u : Fin (d Z) → k) : Pr Z (E Z u) = E Z u := by
  rw [Pr, D_E, mulVec_mulVec, nonsing_inv_mul _ (Ne.isUnit (G_det hZ h)), one_mulVec]

theorem D_sub_Pr (hZ : CR Z) (h : Hyp Z) (x : Mat k n) : D Z (x - Pr Z x) = 0 := by rw [D_sub, D_Pr hZ h, sub_self]
theorem Pr_add (x y : Mat k n) : Pr Z (x + y) = Pr Z x + Pr Z y := by simp [Pr, D_add, mulVec_add, E_add]
theorem Pr_smul (c : k) (x : Mat k n) : Pr Z (c • x) = c • Pr Z x := by simp [Pr, D_smul, mulVec_smul, E_smul]
theorem Pr_of_D {x : Mat k n} (hx : D Z x = 0) : Pr Z x = 0 := by simp [Pr, hx, E]

theorem piZ_eq_sub (hZ : CR Z) (h : Hyp Z) {x : Mat k n} (hx : x ∈ Bz Z) : piZ Z x = x - Pr Z x := by
  obtain ⟨v, hv⟩ := exists_E Z (sub_pi_mem hZ h hx)
  have hP : Pr Z x = x - piZ Z x := by
    conv_lhs => rw [← sub_add_cancel x (piZ Z x)]
    rw [Pr_add, ← hv, Pr_E hZ h, Pr_of_D (D_Z Z (h.pi_mem x)), add_zero, hv]
  rw [hP, sub_sub_cancel]

end AlgPhi2

section TopPhi2
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  (Z : SubM k n)

abbrev TT : Type := ↥(LinearMap.ker (Dl Z)) × (Fin n → k)
theorem continuous_E : Continuous (E Z) := by
  rw [show E Z = fun u => ∑ j, u j • ee Z j from funext (E_apply Z)]; fun_prop
theorem continuous_D : Continuous (D Z) :=
  continuous_pi fun _ => (continuous_const.matrix_mul continuous_id).matrix_trace
theorem continuous_Pr : Continuous (Pr Z) := (continuous_E Z).comp (continuous_const.matrix_mulVec (continuous_D Z))

variable {Z} (hZ : CR Z) (h : Hyp Z)

def Hb : Sp k n ≃ₜ TT Z × (Fin (d Z) → k) where
  toFun p := ((⟨p.1 - Pr Z p.1, D_sub_Pr hZ h _⟩, p.2), D Z p.1)
  invFun q := (q.1.1.1 + E Z ((G Z)⁻¹ *ᵥ q.2), q.1.2)
  left_inv p := Prod.ext (by show p.1 - Pr Z p.1 + Pr Z p.1 = p.1; exact sub_add_cancel _ _) rfl
  right_inv := fun ⟨⟨⟨y, hy⟩, v⟩, w⟩ => Prod.ext (Prod.ext (Subtype.ext (by
    show _ - Pr Z _ = y; rw [Pr_add, Pr_of_D hy, Pr_E hZ h, zero_add, add_sub_cancel_right])) rfl) (by
    show D Z (y + E Z ((G Z)⁻¹ *ᵥ w)) = w
    rw [D_add, show D Z y = 0 from hy, zero_add, D_E, mulVec_mulVec, mul_nonsing_inv _ (Ne.isUnit (G_det hZ h)),
      one_mulVec])
  continuous_toFun :=
    ((continuous_fst.sub ((continuous_Pr Z).comp continuous_fst)).subtype_mk _).prodMk continuous_snd |>.prodMk
      ((continuous_D Z).comp continuous_fst)
  continuous_invFun :=
    ((continuous_subtypeVal.comp (continuous_fst.comp continuous_fst)).add
      ((continuous_E Z).comp (continuous_const.matrix_mulVec continuous_snd))).prodMk
      (continuous_snd.comp continuous_fst)

def Gm : (Fin (d Z) → k) ≃ₜ (Fin (d Z) → k) where
  toFun u := G Z *ᵥ u
  invFun u := (G Z)⁻¹ *ᵥ u
  left_inv u := by simp [mulVec_mulVec, nonsing_inv_mul _ (Ne.isUnit (G_det hZ h))]
  right_inv u := by simp [mulVec_mulVec, mul_nonsing_inv _ (Ne.isUnit (G_det hZ h))]
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

def F1 : TT Z × (Fin (d Z) → k) ≃ₜ Sp k n := ((Homeomorph.refl (TT Z)).prodCongr (Gm hZ h)).trans (Hb hZ h).symm

theorem real_test_function_apply (q : TT Z × (Fin (d Z) → k)) : F1 hZ h q = (q.1.1.1 + E Z q.2, q.1.2) := by
  show (q.1.1.1 + E Z ((G Z)⁻¹ *ᵥ (G Z *ᵥ q.2)), q.1.2) = _
  rw [mulVec_mulVec, nonsing_inv_mul _ (Ne.isUnit (G_det hZ h)), one_mulVec]

end TopPhi2

section Phi2Meas
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {Z : SubM k n} [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure]
  (hZ : CR Z) (h : Hyp Z)
include hZ h

def phi0 (f : Sp k n → ℂ) : Sp k n → ℂ :=
  fun p => GlobalTheory.SplitDict.pf ψ (Measure.pi fun _ : Fin (d Z) => ν) (fun q => f (F1 hZ h q)) (Hb hZ h p)

theorem characteristic_function_integral_apply (f : Sp k n → ℂ) (p : Sp k n) :
    phi0 ψ ν hZ h f p = ∫ u, f (p.1 - Pr Z p.1 + E Z u, p.2) * (ψ (u ⬝ᵥ D Z p.1) : ℂ) ∂(Measure.pi fun _ => ν) := by
  simp [phi0, GlobalTheory.SplitDict.pf, real_test_function_apply, Hb]

theorem test_vector_mem_schwartz_bruhat {c : kˣ} (hc : HasConductor ψ c) {f : Sp k n → ℂ} (hf : f ∈ SuppUniv k n) :
    phi0 ψ ν hZ h f ∈ SuppUniv k n := by
  have hpf := GlobalTheory.SplitDict.pf_mem_SB (Measure.pi fun _ : Fin (d Z) => ν) hc
    (f := fun q => f (F1 hZ h q)) ⟨hf.1.1.comp_continuous (F1 hZ h).continuous, hf.1.2.comp_homeomorph (F1 hZ h)⟩
  exact ⟨⟨hpf.1.comp_continuous (Hb hZ h).continuous, hpf.2.comp_homeomorph (Hb hZ h)⟩, subset_univ _⟩

theorem integrable_slice (hψ : Continuous ψ) {f : Sp k n → ℂ} (hf : f ∈ SuppUniv k n) (p : Sp k n) :
    Integrable (fun u => f (p.1 - Pr Z p.1 + E Z u, p.2) * (ψ (u ⬝ᵥ D Z p.1) : ℂ)) (Measure.pi fun _ => ν) := by
  have hslice : (fun x => f (p.1 - Pr Z p.1 + E Z x, p.2)) = fun x => (f ∘ F1 hZ h) ((Hb hZ h p).1, x) := by
    funext x; simp [real_test_function_apply, Hb]
  have hcs : HasCompactSupport (fun x => f (p.1 - Pr Z p.1 + E Z x, p.2)) :=
    HasCompactSupport.intro ((hf.1.2.comp_homeomorph (F1 hZ h)).isCompact.image continuous_snd) fun x hx =>
      by_contra fun hne => hx ⟨((Hb hZ h p).1, x), subset_tsupport _ (by
        show (f ∘ F1 hZ h) ((Hb hZ h p).1, x) ≠ 0; rwa [← congrFun hslice x]), rfl⟩
  exact Continuous.integrable_of_hasCompactSupport (Continuous.mul
    (by rw [hslice]; exact (hf.1.1.continuous.comp (F1 hZ h).continuous).comp (Continuous.prodMk_right _))
    (by fun_prop)) (hcs.mul_right (f' := fun u => (ψ (u ⬝ᵥ D Z p.1) : ℂ)))

def phiS (hψ : Continuous ψ) : (SuppUniv k n) →ₗ[ℂ] (Sp k n → ℂ) where
  toFun f := phi0 ψ ν hZ h f.1
  map_add' f g := funext fun p => by
    simp only [Submodule.coe_add, Pi.add_apply, characteristic_function_integral_apply, add_mul]
    exact integral_add (integrable_slice ψ ν hZ h hψ f.2 p) (integrable_slice ψ ν hZ h hψ g.2 p)
  map_smul' c f := funext fun p => by
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, characteristic_function_integral_apply, mul_assoc,
      RingHom.id_apply]
    exact integral_const_mul _ _

end Phi2Meas
end Phi2
end PositivityTheory.RgUd.T.Nil.Four
end

section
open Matrix MeasureTheory GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil ValuativeRel

namespace PositivityTheory.RgUd.T.Nil.Four.Phi2

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil

section Alg

variable {k : Type} [Field k] {n : ℕ} {Z : SubM k n}

theorem inv_mem_Gz {g : GLn k n} (hg : g ∈ Gz Z) : g⁻¹ ∈ Gz Z := Gz_inv_mem hg

theorem conj_mem_Bz {g : GLn k n} (hg : g ∈ Gz Z) {w : Mat k n} (hw : w ∈ Bz Z) :
    g.val * w * g⁻¹.val ∈ Bz Z := conj_mem_Bz_shared hg hw

theorem conj_mem_B0 {g : GLn k n} (hg : g ∈ Gz Z) {w : Mat k n} (hw : w ∈ B0 Z) :
    g.val * w * g⁻¹.val ∈ B0 Z :=
  ⟨conj_mem_Bz hg hw.1, by show qZ Z (g.val * w * g⁻¹.val) = 0; rw [PositivityTheory.RgUd.T.Nil.qZ_conj_s Z hg w]; exact hw.2⟩

private theorem tr_conj (A P g g' : Mat k n) : trace (A * (g * P * g')) = trace (g' * A * g * P) := by
  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]

private theorem trace_conj (g : GLn k n) (A : Mat k n) : trace (g.val * A * g⁻¹.val) = trace A := by
  rw [trace_mul_comm, ← mul_assoc, Units.inv_mul, one_mul]

def adL {g : GLn k n} (hg : g ∈ Gz Z) : (Fin (d Z) → k) →ₗ[k] (Fin (d Z) → k) where
  toFun u := (bas Z).equivFun ⟨g.val * E Z u * g⁻¹.val, conj_mem_B0 hg (E_mem Z u)⟩
  map_add' u u' := by rw [← map_add]; congr 1; ext1; simp [E_add, mul_add, add_mul]
  map_smul' c u := by rw [← map_smul]; congr 1; ext1; simp [E_smul]

theorem E_adL {g : GLn k n} (hg : g ∈ Gz Z) (u : Fin (d Z) → k) :
    E Z (adL hg u) = g.val * E Z u * g⁻¹.val := by simp [adL, E]

theorem dot_conj {g : GLn k n} (hg : g ∈ Gz Z) (u : Fin (d Z) → k) (x : Mat k n) :
    adL hg u ⬝ᵥ D Z (g.val * x * g⁻¹.val) = u ⬝ᵥ D Z x := by
  rw [dot_D, dot_D, E_adL, show g.val * E Z u * g⁻¹.val * (g.val * x * g⁻¹.val) = g.val * (E Z u * x) * g⁻¹.val by
    simp only [mul_assoc, Units.inv_mul_cancel_left], trace_conj]

def adM {g : GLn k n} (hg : g ∈ Gz Z) : Matrix (Fin (d Z)) (Fin (d Z)) k := LinearMap.toMatrix' (adL hg)

theorem adM_mulVec {g : GLn k n} (hg : g ∈ Gz Z) (u : Fin (d Z) → k) : adM hg *ᵥ u = adL hg u :=
  LinearMap.toMatrix'_mulVec _ _

theorem dot_G (u u' : Fin (d Z) → k) : u ⬝ᵥ (G Z *ᵥ u') = trace (E Z u * E Z u') := by rw [← D_E, dot_D]

theorem gram_adM {g : GLn k n} (hg : g ∈ Gz Z) : (adM hg)ᵀ * G Z * adM hg = G Z := by
  have key : ∀ u u', u ⬝ᵥ (((adM hg)ᵀ * G Z * adM hg) *ᵥ u') = u ⬝ᵥ (G Z *ᵥ u') := fun u u' => by
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose, adM_mulVec, adM_mulVec, dot_G, dot_G,
      E_adL, E_adL, show g.val * E Z u * g⁻¹.val * (g.val * E Z u' * g⁻¹.val) = g.val * (E Z u * E Z u') * g⁻¹.val by
        simp only [mul_assoc, Units.inv_mul_cancel_left], trace_conj]
  ext i j; simpa [single_dotProduct, mulVec_single_one] using key (Pi.single i 1) (Pi.single j 1)

def Refl (p : Sp k n) : Sp k n := (p.1 - (2 : k) • Pr Z p.1, p.2)

private def Tu (t : kˣ) : GL (Fin (d Z)) k :=
  Units.map (Matrix.scalar (Fin (d Z)) : k →+* Matrix (Fin (d Z)) (Fin (d Z)) k) t

private theorem Tu_mulVec (t : kˣ) (u : Fin (d Z) → k) : (Tu (Z := Z) t).val *ᵥ u = (t : k) • u :=
  funext fun _ => by simp [Tu, Matrix.scalar_apply, mulVec_diagonal]

private theorem Tu_det (t : kˣ) : Matrix.GeneralLinearGroup.det (Tu (Z := Z) t) = t ^ d Z := by
  ext; simp [Tu, Matrix.scalar_apply, Matrix.GeneralLinearGroup.val_det_apply, det_diagonal]

variable (hZ : CR Z) (h : Hyp Z)
include hZ h

private theorem Pr_unique {w y : Mat k n} (hw : w ∈ B0 Z) (hD : D Z w = D Z y) : w = Pr Z y := by
  obtain ⟨u, rfl⟩ := exists_E Z hw
  show E Z u = E Z ((G Z)⁻¹ *ᵥ D Z y)
  congr 1
  have h1 : G Z *ᵥ ((G Z)⁻¹ *ᵥ D Z y) = D Z y := by simpa [Pr, D_E] using D_Pr hZ h y
  rw [D_E] at hD
  exact sub_eq_zero.mp (G_inj hZ h (by rw [Matrix.mulVec_sub, hD, h1, sub_self]))

private theorem Pr_Pr (x : Mat k n) : Pr Z (Pr Z x) = Pr Z x := Pr_E hZ h _

private theorem tr_Pr {w : Mat k n} (hw : w ∈ B0 Z) (x : Mat k n) : trace (w * x) = trace (w * Pr Z x) := by
  obtain ⟨u, rfl⟩ := exists_E Z hw
  have h0 := D_sub_Pr hZ h x
  have hz : trace (E Z u * (x - Pr Z x)) = 0 := by
    rw [E_apply, Finset.sum_mul, Matrix.trace_sum]
    exact Finset.sum_eq_zero fun j _ => by
      rw [Matrix.smul_mul, Matrix.trace_smul, show trace (ee Z j * (x - Pr Z x)) = 0 from congrFun h0 j, smul_zero]
  exact sub_eq_zero.mp (by rwa [Matrix.mul_sub, Matrix.trace_sub] at hz)

private theorem Pr_conj {g : GLn k n} (hg : g ∈ Gz Z) (x : Mat k n) :
    Pr Z (g.val * x * g⁻¹.val) = g.val * Pr Z x * g⁻¹.val := by
  refine (Pr_unique hZ h (conj_mem_B0 hg (E_mem Z _)) (funext fun j => ?_)).symm
  show trace (ee Z j * (g.val * Pr Z x * g⁻¹.val)) = trace (ee Z j * (g.val * x * g⁻¹.val))
  rw [tr_conj, tr_conj]
  have hm := conj_mem_B0 (inv_mem_Gz hg) ((bas Z) j).2
  rw [inv_inv] at hm
  exact (tr_Pr hZ h hm x).symm

theorem det_adM_sq {g : GLn k n} (hg : g ∈ Gz Z) : (adM hg).det ^ 2 = 1 := by
  have h1 := congrArg Matrix.det (gram_adM hg)
  rw [det_mul, det_mul, det_transpose] at h1
  have h2 : ((adM hg).det ^ 2 - 1) * (G Z).det = 0 := by linear_combination h1
  exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right (G_det hZ h))

def adU {g : GLn k n} (hg : g ∈ Gz Z) : GL (Fin (d Z)) k :=
  Matrix.nonsingInvUnit (adM hg) (Ne.isUnit fun h0 => by have := det_adM_sq hZ h hg; rw [h0] at this; norm_num at this)

def Gu : GL (Fin (d Z)) k := Matrix.nonsingInvUnit (G Z) (Ne.isUnit (G_det hZ h))

theorem Refl_Refl (p : Sp k n) : Refl (Z := Z) (Refl (Z := Z) p) = p := by
  have hP : Pr Z (p.1 - (2 : k) • Pr Z p.1) = -Pr Z p.1 := by
    rw [sub_eq_add_neg, Pr_add, ← neg_smul, Pr_smul, Pr_Pr hZ h]; module
  obtain ⟨x, v⟩ := p
  simp only [Refl] at hP ⊢
  rw [hP]; ext <;> simp

end Alg

section LocalField

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ} {Z : SubM k n} (hZ : CR Z) (h : Hyp Z)
include hZ h

theorem distribHaarChar_adU {g : GLn k n} (hg : g ∈ Gz Z) :
    (distribHaarChar k (Matrix.GeneralLinearGroup.det (adU hZ h hg)) : NNReal) = 1 := by
  set u := Matrix.GeneralLinearGroup.det (adU hZ h hg)
  have hu : u ^ 2 = 1 := Units.ext (by
    simp only [u, adU, Units.val_pow_eq_pow_val, Units.val_one, Matrix.GeneralLinearGroup.val_det_apply]
    exact det_adM_sq hZ h hg)
  exact (pow_eq_one_iff_of_nonneg (by positivity) two_ne_zero).1 (by rw [← map_pow, hu, map_one])

theorem partial_fourier_first_coordinates (q : TT Z × (Fin (d Z) → k)) : Hb hZ h (F1 hZ h q) = (q.1, G Z *ᵥ q.2) := by
  simp only [F1, Homeomorph.trans_apply, Homeomorph.apply_symm_apply]; rfl

end LocalField

section LocalFieldMeas

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ} {Z : SubM k n}
  [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure]
  (hZ : CR Z) (h : Hyp Z)
include hZ h

private def mulVecMeasEquiv (A : Matrix (Fin (d Z)) (Fin (d Z)) k) (hU : IsUnit A.det) :
    (Fin (d Z) → k) ≃ᵐ (Fin (d Z) → k) where
  toFun u := A *ᵥ u
  invFun u := A⁻¹ *ᵥ u
  left_inv u := by simp [mulVec_mulVec, nonsing_inv_mul _ hU]
  right_inv u := by simp [mulVec_mulVec, mul_nonsing_inv _ hU]
  measurable_toFun := (continuous_const.matrix_mulVec continuous_id).measurable
  measurable_invFun := (continuous_const.matrix_mulVec continuous_id).measurable

theorem fourier_transform_vanishes_on_fibre (f : Sp k n → ℂ) {y : Fin (Module.finrank k Z) → k}
    (hf0 : ∀ q ∈ Fib Z y, f q = 0) {p : Sp k n} (hp : p ∈ Fib Z y) : phi0 ψ ν hZ h f p = 0 := by
  rw [characteristic_function_integral_apply]
  have hz : ∀ u, f (p.1 - Pr Z p.1 + E Z u, p.2) = 0 := fun u => hf0 _ <| by
    obtain ⟨⟨hB, hq⟩, -⟩ := hp
    have hw : E Z u - Pr Z p.1 ∈ B0 Z := Submodule.sub_mem _ (E_mem Z u) (E_mem Z _)
    have heq : p.1 - Pr Z p.1 + E Z u = p.1 + (E Z u - Pr Z p.1) := by abel
    refine ⟨⟨by show p.1 - Pr Z p.1 + E Z u ∈ BzL Z; rw [heq]; exact (BzL Z).add_mem hB hw.1, ?_⟩, Set.mem_univ _⟩
    show qZ Z (p.1 - Pr Z p.1 + E Z u) = y
    rw [heq]; have hadd := (qL Z).map_add p.1 (E Z u - Pr Z p.1)
    rw [LinearMap.mem_ker.1 hw.2, add_zero] at hadd; exact hadd.trans hq
  simp [hz]

theorem fourier_transform_equivariant {g : GLn k n} (hg : g ∈ Gz Z) (f : Sp k n → ℂ) (p : Sp k n) :
    phi0 ψ ν hZ h (fun q => f (act g q)) p = phi0 ψ ν hZ h f (act g p) := by
  have hU : IsUnit (adM hg).det := isUnit_iff_ne_zero.mpr fun h0 => by
    have := det_adM_sq hZ h hg; rw [h0] at this; simp at this
  let e := mulVecMeasEquiv (Z := Z) (adM hg) hU
  have hmap : Measure.map e (Measure.pi fun _ : Fin (d Z) => ν) = Measure.pi fun _ => ν := by
    have := GlobalTheory.WeilM.smul_map_mulVec_pi ν (adM hg) (GeneralLinearGroup.det (adU hZ h hg)) rfl
    rw [distribHaarChar_adU] at this; simpa [e, mulVecMeasEquiv] using this
  rw [characteristic_function_integral_apply, characteristic_function_integral_apply]
  conv_rhs => rw [← hmap, e.measurableEmbedding.integral_map]
  congr 1; funext u
  simp only [act, e, mulVecMeasEquiv, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, adM_mulVec, E_adL, Pr_conj hZ h hg,
    dot_conj]
  congr 3; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul]

theorem fourier_transform_preserves_compact {c : kˣ} (hc : HasConductor ψ c) {f : Sp k n → ℂ}
    (hf : f ∈ supportedIn (UU : Set (Sp k n))) : phi0 ψ ν hZ h f ∈ supportedIn (UU : Set (Sp k n)) := by
  refine ⟨(test_vector_mem_schwartz_bruhat ψ ν hZ h hc (f := f) ⟨hf.1, Set.subset_univ _⟩).1, fun p hp => ?_⟩
  by_contra hp2; apply hp
  have h0 : p.2 = 0 := not_not.mp hp2
  rw [characteristic_function_integral_apply]
  have hz : ∀ u, f (p.1 - Pr Z p.1 + E Z u, p.2) = 0 := fun u => by_contra fun hne => hf.2 hne h0
  simp [hz]

theorem pf_G (F : TT Z × (Fin (d Z) → k) → ℂ) (z : TT Z × (Fin (d Z) → k)) :
    ∫ u, F (z.1, G Z *ᵥ u) * (ψ (u ⬝ᵥ z.2) : ℂ) ∂(Measure.pi fun _ => ν) =
      ((distribHaarChar k (Matrix.GeneralLinearGroup.det (Gu hZ h)) : ℝ) : ℂ)⁻¹ *
        GlobalTheory.SplitDict.pf ψ (Measure.pi fun _ => ν) F (z.1, (G Z)⁻¹ *ᵥ z.2) := by
  have hU : IsUnit (G Z).det := isUnit_iff_ne_zero.mpr (G_det hZ h)
  set c := distribHaarChar k (Matrix.GeneralLinearGroup.det (Gu hZ h)) with hcdef
  have hc : c ≠ 0 := (distribHaarChar_pos).ne'
  let e := mulVecMeasEquiv (Z := Z) (G Z) hU
  have hsm := GlobalTheory.WeilM.smul_map_mulVec_pi ν (G Z) (Matrix.GeneralLinearGroup.det (Gu hZ h)) rfl
  rw [← hcdef] at hsm
  have hmap : Measure.map e (Measure.pi fun _ : Fin (d Z) => ν) = (c : ENNReal)⁻¹ • Measure.pi fun _ => ν := by
    show Measure.map (G Z).mulVec _ = _
    conv_rhs => rw [← hsm]
    rw [smul_smul, ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.mpr hc) ENNReal.coe_ne_top, one_smul]
  let H : (Fin (d Z) → k) → ℂ := fun x => F (z.1, x) * (ψ (x ⬝ᵥ (G Z)⁻¹ *ᵥ z.2) : ℂ)
  have hH : ∀ u, F (z.1, G Z *ᵥ u) * (ψ (u ⬝ᵥ z.2) : ℂ) = H (e u) := fun u => by
    show _ = F (z.1, G Z *ᵥ u) * (ψ ((G Z *ᵥ u) ⬝ᵥ (G Z)⁻¹ *ᵥ z.2) : ℂ)
    rw [dotProduct_mulVec, vecMul_mulVec, ← Matrix.mulVec_transpose, G_symm, mul_nonsing_inv _ hU,
      transpose_one, one_mulVec]
  rw [integral_congr_ae (ae_of_all _ hH), ← e.measurableEmbedding.integral_map, hmap, integral_smul_measure]
  simp [GlobalTheory.SplitDict.pf, H]

theorem fourier_transform_involution {c : kˣ} (hc : HasConductor ψ c) {f : Sp k n → ℂ}
    (hf : f ∈ SuppUniv k n) (p : Sp k n) :
    phi0 ψ ν hZ h (phi0 ψ ν hZ h f) p =
      ((distribHaarChar k (Matrix.GeneralLinearGroup.det (Gu hZ h)) : ℝ) : ℂ)⁻¹ *
        ((((ν.real (𝒪[k] : Set k) ^ 2 * nabs k c) ^ (d Z) : ℝ)) : ℂ) * f (Refl (Z := Z) p) := by
  have h1 : (fun q => f (F1 hZ h q)) ∈ SB (TT Z × (Fin (d Z) → k)) :=
    (GlobalTheory.SplitDict.bijOn_comp (F1 hZ h)).1 hf.1
  have e : ∀ q, phi0 ψ ν hZ h f (F1 hZ h q) =
      GlobalTheory.SplitDict.pf ψ (Measure.pi fun _ => ν) (fun q => f (F1 hZ h q)) (q.1, G Z *ᵥ q.2) := fun q => by
    show GlobalTheory.SplitDict.pf _ _ _ (Hb hZ h (F1 hZ h q)) = _; rw [partial_fourier_first_coordinates]
  show GlobalTheory.SplitDict.pf ψ _ (fun q => phi0 ψ ν hZ h f (F1 hZ h q)) (Hb hZ h p) = _
  simp only [e]
  show ∫ u, GlobalTheory.SplitDict.pf ψ (Measure.pi fun _ => ν) (fun q => f (F1 hZ h q)) ((Hb hZ h p).1, G Z *ᵥ u) *
      (ψ (u ⬝ᵥ (Hb hZ h p).2) : ℂ) ∂(Measure.pi fun _ => ν) = _
  rw [pf_G ψ ν hZ h, GlobalTheory.SplitDict.pf_pf ν hc h1]
  simp only [real_test_function_apply, Fintype.card_fin]
  have e2 : ((Hb hZ h p).1.1 : Mat k n) + E Z (-((G Z)⁻¹ *ᵥ (Hb hZ h p).2)) = p.1 - (2 : k) • Pr Z p.1 := by
    rw [E_neg]; show p.1 - Pr Z p.1 + -(E Z ((G Z)⁻¹ *ᵥ D Z p.1)) = _; rw [← Pr, two_smul]; abel
  rw [e2, show (Hb hZ h p).1.2 = p.2 from rfl]; simp only [Refl]; ring

theorem fourier_transform_scaling (t : kˣ) (f : Sp k n → ℂ) {p : Sp k n} (hp : p ∈ Bz Z ×ˢ Set.univ) :
    phi0 ψ ν hZ h f (sig Z t p) =
      ((((nabs k t)⁻¹ ^ d Z : ℝ)) : ℂ) * phi0 ψ ν hZ h (fun q => f (sig Z t⁻¹ q)) p := by
  obtain ⟨x, v⟩ := p
  have hDy : D Z (x - Pr Z x) = 0 := D_sub_Pr hZ h x
  have hPy : Pr Z (x - Pr Z x) = 0 := Pr_of_D hDy
  have hsig : sig Z t (x, v) = (x - Pr Z x + (t : k) • Pr Z x, v) := by
    simp only [sig, piZ_eq_sub hZ h hp.1, sub_sub_cancel]
  rw [hsig, characteristic_function_integral_apply, characteristic_function_integral_apply]
  have hP : Pr Z (x - Pr Z x + (t : k) • Pr Z x) = (t : k) • Pr Z x := by
    rw [Pr_add, hPy, Pr_smul, Pr_Pr hZ h, zero_add]
  have hD : D Z (x - Pr Z x + (t : k) • Pr Z x) = (t : k) • D Z x := by
    rw [D_add, hDy, D_smul, D_Pr hZ h, zero_add]
  simp only [hP, hD, add_sub_cancel_right]
  have hpi2 : ∀ u, piZ Z (x - Pr Z x + E Z u) = x - Pr Z x := fun u => by
    have hm : x - Pr Z x + E Z u ∈ BzL Z :=
      (BzL Z).add_mem ((BzL Z).sub_mem (show x ∈ BzL Z from hp.1) (show Pr Z x ∈ B0 Z from E_mem Z _).1) (E_mem Z u).1
    rw [piZ_eq_sub hZ h hm, Pr_add, hPy, Pr_E hZ h, zero_add, add_sub_cancel_right]
  simp only [show ∀ u, sig Z t⁻¹ (x - Pr Z x + E Z u, v) = (x - Pr Z x + E Z ((t⁻¹ : k) • u), v) from fun u => by
    simp only [sig, hpi2, add_sub_cancel_left, E_smul, Units.val_inv_eq_inv_val]]
  have key := GlobalTheory.WeilM.integral_comp_mulVec ν (Tu (Z := Z) t)
    (fun u => f (x - Pr Z x + E Z ((t⁻¹ : k) • u), v) * (ψ (u ⬝ᵥ D Z x) : ℂ))
  simp only [Tu_mulVec, Tu_det, map_pow, smul_smul, inv_mul_cancel₀ t.ne_zero, one_smul, smul_dotProduct,
    ← dotProduct_smul] at key
  rw [← key]
  have hn : (nabs k t : ℝ) = ((distribHaarChar k t : NNReal) : ℝ) := rfl
  have hposC : ((nabs k t : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (show (nabs k t : ℝ) ≠ 0 by rw [hn]; exact_mod_cast distribHaarChar_pos.ne')
  rw [NNReal.coe_pow, ← hn]; push_cast
  rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hposC, one_pow, one_mul]

end LocalFieldMeas

end PositivityTheory.RgUd.T.Nil.Four.Phi2
end

section
open Matrix MeasureTheory GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil ValuativeRel

namespace PositivityTheory.RgUd.T.Nil.Four

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem supp_congr {n : ℕ} {Z : SubM k n} {ξ : DistS k n} (h : Supp ξ (Bz Z ×ˢ Set.univ)) {f g : Sp k n → ℂ}
    (hf : f ∈ SuppUniv k n) (hg : g ∈ SuppUniv k n) (e : ∀ p ∈ Bz Z ×ˢ Set.univ, f p = g p) : ξ f = ξ g := by
  have := h (f - g) ((supportedIn Set.univ).sub_mem hf hg) fun p hp => by simp [e p hp]
  rwa [map_sub, sub_eq_zero] at this

theorem fourP_of (hΦ : PhiP (k := k)) (hC : CompP (k := k)) : FourP (k := k) := by
  intro n Z hZ
  obtain ⟨Φ, Φ', h1, h2, h3, h4, h5, h6, h7, h8⟩ := hΦ n Z hZ
  obtain ⟨hCs, hCa, -, -⟩ := hC n Z hZ
  let F : DistS k n →ₗ[ℂ] DistS k n :=
    { toFun := fun ξ => ξ ∘ₗ Φ, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  refine ⟨F, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun ξ hξ f hf hz => hξ _ (h1 f hf) fun p hp =>
      h3 f hf (qZ Z p.1) (fun q hq => hz q ⟨hq.1.1, Set.mem_univ _⟩) p ⟨⟨hp.1, rfl⟩, Set.mem_univ _⟩
  · exact fun ξ y hξ f hf hz => hξ _ (h1 f hf) (h3 f hf y hz)
  · intro ξ hξ hinv g hg f hf
    rw [show F ξ _ = ξ (Φ _) from rfl, show F ξ f = ξ (Φ f) from rfl,
      supp_congr hξ (h1 _ (hCa g f hf)) (hCa g _ (h1 f hf)) (fun p hp => h4 g hg f hf p hp)]
    exact hinv g hg _ (h1 f hf)
  · exact fun ξ hξ => ⟨fun hk f hf => hk _ (h5 f hf), fun hk f hf => by
      have hfu : f ∈ SuppUniv k n := ⟨hf.1, Set.subset_univ _⟩
      rw [← supp_congr hξ (h1 _ (h2 f hfu)) hfu (fun p hp => h7 f hfu p hp)]
      exact hk _ (h6 f hf)⟩
  · exact fun ξ hξ f hf => hξ _ (h1 f hf)
  · intro t ξ hξ f hf
    show ξ (fun q => Φ f (sig Z t q)) = _ * ξ (Φ (fun q => f (sig Z t⁻¹ q)))
    rw [← smul_eq_mul, ← map_smul]
    exact supp_congr hξ (hCs t _ (h1 f hf)) (Submodule.smul_mem _ _ (h1 _ (hCs t⁻¹ f hf)))
      (fun p hp => by rw [Pi.smul_apply, smul_eq_mul]; exact h8 t f hf p hp)

namespace Alg

variable {n : ℕ}

def actH (g : GLn k n) : Sp k n ≃ₜ Sp k n := actH_shared g

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem comp_mem {f : Sp k n → ℂ} (hf : f ∈ SuppUniv k n) (e : Sp k n ≃ₜ Sp k n) :
    (fun q => f (e q)) ∈ SuppUniv k n :=
  ⟨⟨hf.1.1.comp_continuous e.continuous, hf.1.2.comp_homeomorph e⟩, Set.subset_univ _⟩

theorem compP [CharZero k] : CompP (k := k) := by
  intro n Z hZ
  refine ⟨fun t f hf => comp_mem hf (sigH_s hZ t), fun g f hf => comp_mem hf (actH g), ?_, ?_⟩
  · rintro t ⟨x, v⟩ ⟨hx, -⟩
    refine ⟨fun a ha => ?_, Set.mem_univ _⟩
    have hc := hZ.1 _ ha _ (piZ_mem_s Z x)
    have hx' := hx a ha
    simp only [sig, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, hc, hx']
  · rintro g hg ⟨x, v⟩ ⟨hx, -⟩
    exact ⟨conj_mem_Bz_shared hg hx, Set.mem_univ _⟩

end Alg

namespace Phi2

variable {n : ℕ} {Z : SubM k n}

def ReflH (hZ : CR Z) (h : Hyp Z) : Sp k n ≃ₜ Sp k n where
  toFun := Refl (Z := Z)
  invFun := Refl (Z := Z)
  left_inv := Refl_Refl hZ h
  right_inv := Refl_Refl hZ h
  continuous_toFun :=
    (continuous_fst.sub (((continuous_Pr Z).comp continuous_fst).const_smul (2 : k))).prodMk continuous_snd
  continuous_invFun :=
    (continuous_fst.sub (((continuous_Pr Z).comp continuous_fst).const_smul (2 : k))).prodMk continuous_snd

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem d_eq [CharZero k] (hZ : CR Z) : d Z = dB0 Z := by
  classical
  have hsurj : LinearMap.range ((qL Z).domRestrict (BzL Z)) = ⊤ :=
    LinearMap.range_eq_top.2 fun y => let ⟨c, hc, hcy⟩ := qZ_surj_s hZ y; ⟨⟨c, Z_le_Bz Z hZ hc⟩, hcy⟩
  have hrn := LinearMap.finrank_range_add_finrank_ker ((qL Z).domRestrict (BzL Z))
  rw [hsurj, finrank_top, Module.finrank_fin_fun] at hrn
  have hker : LinearMap.ker ((qL Z).domRestrict (BzL Z)) = (B0 Z).comap (BzL Z).subtype := by
    ext x; simp [B0]
  have e : Module.finrank k (LinearMap.ker ((qL Z).domRestrict (BzL Z))) = Module.finrank k (B0 Z) := by
    rw [hker]; exact (Submodule.comapSubtypeEquivOfLe (inf_le_left : B0 Z ≤ BzL Z)).finrank_eq
  have hC : Module.finrank k (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) =
      Module.finrank k (BzL Z) := by
    have hsub : Subalgebra.toSubmodule (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) = BzL Z :=
      Submodule.ext fun x => Subalgebra.mem_centralizer_iff k
    rw [← Subalgebra.finrank_toSubmodule, hsub]
  unfold d dB0; rw [← e, hC, ← hrn, Nat.add_sub_cancel_left]

theorem phiP [CharZero k] : PhiP (k := k) := by
  intro n Z hZ
  borelize k
  have h : Hyp Z := ⟨fun x => piZ_mem_s Z x, fun x => (piZ_spec_s hZ x).2, fun _ _ hc hq => piZ_eq_s hZ hc hq,
    fun w hw hb => Alg.trB_nondeg hZ hw hb⟩
  obtain ⟨ψ, hψ⟩ := exists_hasConductor_one k
  let ν : Measure k := Measure.addHaar
  have hcomp : ∀ (U : Set (Sp k n)) (e : Sp k n ≃ₜ Sp k n), (∀ x, e x ∈ U → x ∈ U) →
      ∀ f : Sp k n → ℂ, f ∈ supportedIn U → (fun p => f (e p)) ∈ supportedIn U :=
    fun _ e he _ hf => ⟨⟨hf.1.1.comp_continuous e.continuous, hf.1.2.comp_homeomorph e⟩, fun x hx => he x (hf.2 hx)⟩
  have hU : ∀ (e : Sp k n ≃ₜ Sp k n) (f : Sp k n → ℂ), f ∈ SuppUniv k n → (fun p => f (e p)) ∈ SuppUniv k n :=
    fun e => hcomp Set.univ e (fun _ _ => Set.mem_univ _)
  have hRf := hU (ReflH hZ h)
  have hRU := hcomp UU (ReflH hZ h) (fun _ hx => hx)
  obtain ⟨q, hq⟩ := (SuppUniv k n).exists_isCompl
  let Φ : (Sp k n → ℂ) →ₗ[ℂ] Sp k n → ℂ :=
    (phiS ψ ν hZ h hψ.continuous).comp ((SuppUniv k n).projectionOnto q hq)
  have hΦ : ∀ f ∈ SuppUniv k n, Φ f = phi0 ψ ν hZ h f := fun f hf => by
    have e1 : (SuppUniv k n).projectionOnto q hq f = ⟨f, hf⟩ := Submodule.projectionOnto_apply_left hq ⟨f, hf⟩
    simp only [Φ, LinearMap.comp_apply, e1]; rfl
  let κ : ℂ := (((distribHaarChar k (GeneralLinearGroup.det (Gu hZ h)) : NNReal) : ℝ) : ℂ)⁻¹ *
    (((ν.real (𝒪[k] : Set k) ^ 2 * nabs k 1) ^ d Z : ℝ) : ℂ)
  have hχ : (distribHaarChar k (GeneralLinearGroup.det (Gu hZ h)) : NNReal) ≠ 0 :=
    left_ne_zero_of_mul_eq_one (map_mul_eq_one (distribHaarChar k) (mul_inv_cancel (GeneralLinearGroup.det (Gu hZ h))))
  have hν : 0 < ν.real (𝒪[k] : Set k) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos ((ValuativeRel.valuation k).isOpen_integer.measure_ne_zero ν ⟨0, zero_mem _⟩)
      (isCompact_iff_compactSpace.mpr (inferInstance : CompactSpace 𝒪[k])).measure_lt_top.ne
  have hκ : κ ≠ 0 := mul_ne_zero (inv_ne_zero (by exact_mod_cast hχ)) (by
    rw [show nabs k 1 = 1 by simp [nabs], mul_one]; exact_mod_cast pow_ne_zero _ (pow_pos hν 2).ne')
  let Φ' : (Sp k n → ℂ) →ₗ[ℂ] Sp k n → ℂ := κ⁻¹ • (Φ.comp (LinearMap.funLeft ℂ ℂ (Refl (Z := Z))))
  have hΦ' : ∀ f ∈ SuppUniv k n, Φ' f = κ⁻¹ • phi0 ψ ν hZ h (fun p => f (Refl (Z := Z) p)) := fun f hf => by
    change κ⁻¹ • Φ (fun p => f (ReflH hZ h p)) = _; rw [hΦ _ (hRf f hf)]; rfl
  refine ⟨Φ, Φ', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun f hf => hΦ f hf ▸ test_vector_mem_schwartz_bruhat ψ ν hZ h hψ hf
  · exact fun f hf => hΦ' f hf ▸ Submodule.smul_mem _ _ (test_vector_mem_schwartz_bruhat ψ ν hZ h hψ (hRf f hf))
  · exact fun f hf y hy p hp => hΦ f hf ▸ fourier_transform_vanishes_on_fibre ψ ν hZ h f hy hp
  · intro g hg f hf p _
    rw [hΦ f hf, hΦ (fun q => f (act g q)) (hU (Alg.actH g) f hf)]
    exact fourier_transform_equivariant ψ ν hZ h hg f p
  · exact fun f hf => hΦ f (supportedIn_mono (Set.subset_univ _) hf) ▸
      fourier_transform_preserves_compact ψ ν hZ h hψ hf
  · exact fun f hf => hΦ' f (supportedIn_mono (Set.subset_univ _) hf) ▸
      Submodule.smul_mem _ _ (fourier_transform_preserves_compact ψ ν hZ h hψ (hRU f hf))
  · intro f hf p _
    have hR : (fun p => f (Refl (Z := Z) p)) ∈ SuppUniv k n := hRf f hf
    rw [hΦ' f hf, map_smul, hΦ _ (test_vector_mem_schwartz_bruhat ψ ν hZ h hψ hR), Pi.smul_apply,
      fourier_transform_involution ψ ν hZ h hψ hR p, Refl_Refl hZ h, smul_eq_mul, ← mul_assoc]
    change κ⁻¹ * κ * f p = f p; rw [inv_mul_cancel₀ hκ, one_mul]
  · intro t f hf p hp
    rw [hΦ f hf, hΦ (fun q => f (sig Z t⁻¹ q)) (hU (sigH_s hZ t⁻¹) f hf), ← d_eq hZ]
    exact fourier_transform_scaling ψ ν hZ h t f hp

end Phi2

namespace Final

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem fourP [CharZero k] : FourP (k := k) := fourP_of Phi2.phiP Alg.compP

theorem locQ : LocQ (k := k) := locQ_pf

end Final

end PositivityTheory.RgUd.T.Nil.Four
end
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Fourier =====

-- ===== clump member: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.ModulusInduction =====
-- clump-header: {"m": "Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.ModulusInduction", "h": "module\n\npublic import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.CentralizerReps\npublic import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Fourier\npublic import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.ModulusBounds\npublic import GroundTheory.AutomorphicForms.WhittakerOrbit\npublic import Mathlib.GroupTheory.CosetCover\nimport Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected\n\n"}
section -- clump:auto
@[expose] public section
noncomputable section
set_option linter.unusedSectionVars false

section
open Polynomial

namespace PositivityTheory.RgUd.T.Nil.Asm

section

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem pow_mem (K : Submodule ℂ M) (R : Module.End ℂ M) (hK : ∀ m ∈ K, R m ∈ K) :
    ∀ (j : ℕ), ∀ m ∈ K, (R ^ j) m ∈ K
  | 0, _, hm => by simpa using hm
  | j + 1, m, hm => by rw [pow_succ']; exact hK _ (pow_mem K R hK j m hm)

theorem aeval_mem (K : Submodule ℂ M) (R : Module.End ℂ M) (hK : ∀ m ∈ K, R m ∈ K) (p : ℂ[X]) :
    ∀ m ∈ K, (aeval R p) m ∈ K := by
  induction p using Polynomial.induction_on' with
  | add _ _ hp hq =>
    intro m hm
    rw [map_add (f := _), LinearMap.add_apply]
    exact K.add_mem (hp m hm) (hq m hm)
  | monomial j _ =>
    intro m hm
    rw [aeval_monomial, Algebra.algebraMap_eq_smul_one]
    exact K.smul_mem _ (pow_mem K R hK j m hm)

theorem isCoprime_list_prod_left {R : Type*} [CommRing R] {ι : Type*} (f : ι → R) (z : R) :
    ∀ l : List ι, (∀ x ∈ l, IsCoprime (f x) z) → IsCoprime (l.map f).prod z
  | [], _ => by simpa using isCoprime_one_left
  | x :: t, h => by
      rw [List.map_cons, List.prod_cons]
      exact (h x List.mem_cons_self).mul_left
        (isCoprime_list_prod_left f z t fun _ hy => h _ (List.mem_cons_of_mem _ hy))

theorem isCoprime_list_prod_right {R : Type*} [CommRing R] {ι : Type*} (f : ι → R) (z : R) (l : List ι)
    (h : ∀ x ∈ l, IsCoprime z (f x)) : IsCoprime z (l.map f).prod :=
  (isCoprime_list_prod_left f z l fun x hx => (h x hx).symm).symm

theorem isCoprime_lin (α β γ : ℂ) (h : β - γ * α ≠ 0) : IsCoprime (X - C α) (C β - C γ * X) := by
  refine ⟨C (γ / (β - γ * α)), C (1 / (β - γ * α)), ?_⟩
  rw [show C (γ / (β - γ * α)) * (X - C α) + C (1 / (β - γ * α)) * (C β - C γ * X) =
      C ((γ / (β - γ * α)) * (-α) + (1 / (β - γ * α)) * β) + C (γ / (β - γ * α) - 1 / (β - γ * α) * γ) * X by
      simp only [C_add, C_mul, C_neg, C_sub]; ring,
    show γ / (β - γ * α) - 1 / (β - γ * α) * γ = 0 by ring,
    show (γ / (β - γ * α)) * (-α) + (1 / (β - γ * α)) * β = 1 by field_simp; ring]
  simp

theorem aeval_prod_lin (R : Module.End ℂ M) (α : ℝ → ℂ) (a : List ℝ) :
    aeval R ((a.map fun x => X - C (α x)).prod) = ((a.map fun x => R - α x • LinearMap.id).prod : Module.End ℂ M) := by
  rw [map_list_prod, List.map_map]
  exact congrArg List.prod (List.map_congr_left fun _ _ => by
    simp [Algebra.algebraMap_eq_smul_one, Module.End.one_eq_id])

theorem aeval_prod_linear_factors (R : Module.End ℂ M) (β : ℂ) (γ : ℝ → ℂ) (a : List ℝ) :
    aeval R ((a.map fun x => C β - C (γ x) * X).prod) =
      ((a.map fun x => β • LinearMap.id - γ x • R).prod : Module.End ℂ M) := by
  rw [map_list_prod, List.map_map]
  exact congrArg List.prod (List.map_congr_left fun x _ => by
    show aeval R (C β - C (γ x) * X) = β • LinearMap.id - γ x • R
    rw [map_sub, map_mul, aeval_C, aeval_C, aeval_X, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul]; rfl)

theorem pow_mul_prod (R R' : Module.End ℂ M) (hRR : R * R' = 1) (hR'R : R' * R = 1) (β : ℂ) (γ : ℝ → ℂ) :
    ∀ l : List ℝ, R ^ l.length * ((l.map fun x => β • R' - γ x • (1 : Module.End ℂ M)).prod) =
      (l.map fun x => β • (1 : Module.End ℂ M) - γ x • R).prod
  | [] => by simp
  | x :: t => by
      rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, List.length_cons, pow_succ', mul_assoc]
      have hcm : Commute (R ^ t.length) (β • R' - γ x • (1 : Module.End ℂ M)) :=
        ((Commute.pow_left (hRR.trans hR'R.symm) _).smul_right β).sub_right ((Commute.one_right _).smul_right _)
      rw [← mul_assoc (R ^ t.length), hcm.eq, mul_assoc, pow_mul_prod R R' hRR hR'R β γ t, ← mul_assoc]
      congr 1; rw [mul_sub, mul_smul_comm, hRR, mul_smul_comm, mul_one]

end

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem bez {M : Type*} [AddCommGroup M] [Module ℂ M] (K : Submodule ℂ M) (R R' : M →ₗ[ℂ] M)
    (hRR : R ∘ₗ R' = LinearMap.id) (hR'R : R' ∘ₗ R = LinearMap.id) (hK : ∀ m ∈ K, R m ∈ K) (c : ℝ) (hc : 1 < c)
    (d : ℕ) (a : List ℝ) (ha : ∀ x ∈ a, 2 * x < d) (ζ : M)
    (h1 : ((a.map fun x => R - ((c ^ x : ℝ) : ℂ) • LinearMap.id).prod : Module.End ℂ M) ζ ∈ K)
    (h2 : ((a.map fun x => ((c ^ (d : ℝ) : ℝ) : ℂ) • R' - ((c ^ x : ℝ) : ℂ) • LinearMap.id).prod : Module.End ℂ M) ζ ∈
      K) : ζ ∈ K := by
  set β : ℂ := ((c ^ (d : ℝ) : ℝ) : ℂ)
  set γ : ℝ → ℂ := fun x => ((c ^ x : ℝ) : ℂ)
  have hQ : ((a.map fun x => β • (1 : Module.End ℂ M) - γ x • R).prod : Module.End ℂ M) ζ ∈ K := by
    rw [← pow_mul_prod R R' hRR hR'R β γ a]; exact pow_mem K R hK _ _ h2
  obtain ⟨u, v, huv⟩ : IsCoprime ((a.map fun x => X - C (γ x)).prod) ((a.map fun x => C β - C (γ x) * X).prod) :=
    isCoprime_list_prod_left _ _ a fun x hx =>
      isCoprime_list_prod_right _ _ a fun y hy => isCoprime_lin _ _ _ fun h0 => by
      have hlt : c ^ y * c ^ x < c ^ (d : ℝ) := by
        rw [← Real.rpow_add (by linarith)]; exact Real.rpow_lt_rpow_of_exponent_lt hc (by linarith [ha x hx, ha y hy])
      have h0' : (c ^ (d : ℝ) : ℝ) = c ^ y * c ^ x :=
        Complex.ofReal_injective (by simpa [β, γ] using sub_eq_zero.1 h0)
      linarith
  have key := congrArg (fun p => (aeval (R : Module.End ℂ M) p) ζ) huv
  simp only [map_add (f := _), map_mul, map_one, LinearMap.add_apply] at key
  rw [← show _ + _ = ζ from key]
  exact K.add_mem (aeval_mem K R hK u _ (by rw [aeval_prod_lin R γ a]; exact h1))
    (aeval_mem K R hK v _ (by rw [aeval_prod_linear_factors R β γ a]; convert hQ using 3))

end PositivityTheory.RgUd.T.Nil.Asm
end

section
open Matrix GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil Set Polynomial

namespace PositivityTheory.RgUd.T.Nil.Orb.Oasm

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb

section Alg

variable {k : Type} [Field k] {n : ℕ} {Z : SubM k n}

theorem isNilpotent_iff_pow (M : Mat k n) : IsNilpotent M ↔ M ^ n = 0 := Ozn.isNilpotent_iff_pow M

def C0 (Z : SubM k n) (c : Mat k n) : Set (Sp k n) := {q | q.1 ∈ Bz Z ∧ IsNilpotent (q.1 - c)}

private theorem scaling_on_orbit_closure [CharZero k] (hZ : CR Z) {c : Mat k n} (hc : c ∈ Z) (t : kˣ) {q : Sp k n}
    (hq : q ∈ C0 Z c) : sig Z t q = (c + (t : k) • (q.1 - c), q.2) := by
  have hq' : q.1 - c ∈ Bz Z := fun a ha => by rw [mul_sub, sub_mul, hq.1 a ha, hZ.1 a ha c hc]
  have hp : piZ Z q.1 = c := piZ_eq_s hZ hc (sub_eq_zero.1 (by rw [← qZ_sub_s, qZ_nil_s Z hq' hq.2])).symm
  simp [sig, hp]

private theorem scaling_mem_orbit_closure [CharZero k] (hZ : CR Z) {c : Mat k n} (hc : c ∈ Z) (t : kˣ) {q : Sp k n}
    (hq : q ∈ C0 Z c) : sig Z t q ∈ C0 Z c := by
  rw [scaling_on_orbit_closure hZ hc t hq]
  exact ⟨fun a ha => by
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, hq.1 a ha, hZ.1 a ha c hc],
    by simpa using hq.2.smul (t : k)⟩

theorem action_mem_orbit_closure {c : Mat k n} (hc : c ∈ Z) {g : GLn k n} (hg : g ∈ Gz Z)
    {q : Sp k n} (hq : q ∈ C0 Z c) : act g q ∈ C0 Z c := by
  refine ⟨conj_mem_Bz_shared hg hq.1, ?_⟩
  obtain ⟨m, hm⟩ := hq.2
  refine ⟨m, ?_⟩
  show (g.val * q.1 * g⁻¹.val - c) ^ m = 0
  rw [show g.val * q.1 * g⁻¹.val - c = g.val * (q.1 - c) * g⁻¹.val by rw [mul_sub, sub_mul, conj_mem_Z_shared hg hc],
    conj_pow_shared, hm, mul_zero, zero_mul]

theorem orb_subset_UU {p : Sp k n} (hp : p.2 ≠ 0) : orb Z p ⊆ UU := fun _ ⟨g, _, h⟩ => h ▸ act_snd_ne_s g hp

variable [TopologicalSpace k]

theorem comp_mem_supportedIn (h : Sp k n ≃ₜ Sp k n) {U : Set (Sp k n)} {f : Sp k n → ℂ} (hf : f ∈ supportedIn U) :
    (fun p => f (h p)) ∈ supportedIn (h ⁻¹' U) := comp_mem_supportedIn_shared h hf

theorem isClosed_Bz [IsTopologicalRing k] [T2Space k] : IsClosed (Bz Z) := isClosed_Bz_shared Z

theorem isOpen_UU [T2Space k] : IsOpen (UU (k := k) (n := n)) := isOpen_UU_s

theorem kills_of_suppU {ξ : DistS k n} {D : Set (Sp k n)} (hD : D ∩ UU = ∅) (h : SuppU ξ D) : Kills ξ UU :=
  fun f hf => h f hf fun _ hq => by_contra fun hfq => hD.subset ⟨hq, hf.2 hfq⟩

end Alg

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

local instance t2SpaceLocalField : T2Space k := GlobalTheory.SplitWeil.t2Space k

variable {Z : SubM k n}

private theorem inv_pull [CharZero k] (hZ : CR Z) (t : kˣ) {ξ : DistS k n} (hξ : Inv Z ξ) : Inv Z (pull Z t ξ) :=
  fun g hg f hf => by
    rw [pull_apply_s, pull_apply_s, show (fun p => f (act g (sig Z t p))) = fun p => (fun q => f (sig Z t q)) (act g p)
      from funext fun p => by show f (act g (sig Z t p)) = f (sig Z t (act g p)); rw [sig_act_s Z t hg]]
    exact hξ g hg _ (by simpa using comp_mem_supportedIn (sigH_s hZ t) hf)

private theorem kills_aeval [CharZero k] (hZ : CR Z) (t : kˣ) {ξ : DistS k n} (hξ : Kills ξ UU) (Q : ℂ[X]) :
    Kills (aeval (pull Z t) Q ξ) UU := by
  have hkp : ∀ {η}, Kills η UU → Kills (pull Z t η) UU := fun hη f hf =>
    let h := comp_mem_supportedIn (sigH_s hZ t) hf; hη _ ⟨h.1, fun _ hp => by simpa [sigH_s, sig, UU] using h.2 hp⟩
  induction Q using Polynomial.induction_on' with
  | add _ _ hp hq => exact fun f hf => by simp [hp f hf, hq f hf]
  | monomial m _ =>
    have key : ∀ m : ℕ, Kills (((pull Z t) ^ m : Module.End ℂ _) ξ) UU := fun m => by
      induction m with
      | zero => simpa using hξ
      | succ _ ih => rw [pow_succ', Module.End.mul_eq_comp, LinearMap.comp_apply]; exact hkp ih
    exact fun f hf => by simp [aeval_monomial, key m f hf]

private theorem isClosed_C0 (c : Mat k n) : IsClosed (C0 Z c) := by
  rw [show C0 Z c = Prod.fst ⁻¹' (Bz Z ∩ {x | (x - c) ^ n = 0}) by ext q; simp [C0, isNilpotent_iff_pow]]
  exact (isClosed_Bz.inter (isClosed_eq ((continuous_id.sub continuous_const).pow n) continuous_const)).preimage
    continuous_fst

private theorem support_in_orbit_closure [CharZero k] (h1 : ZNClosed (k := k)) (h2 : FibZN (k := k)) (hZ : CR Z)
    {c : Mat k n} (hc : c ∈ Z) {ξ : DistS k n} (hs : Supp ξ (Fib Z (qZ Z c)))
    (hk : Kills ξ (UU ∩ {p | p.1 ∉ ZN Z})) : SuppU ξ (C0 Z c) := by
  have : TotallyDisconnectedSpace k := totallyDisconnectedSpace_localField
  have : LocallyCompactSpace (Mat k n) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → k))
  have : T2Space (Mat k n) := inferInstanceAs (T2Space (Fin n → Fin n → k))
  have : TotallyDisconnectedSpace (Mat k n) := inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → k))
  intro f hf h0
  have hKF : Function.support f ∩ (ZN Z ×ˢ Set.univ) ⊆ (Fib Z (qZ Z c))ᶜ := fun q ⟨hq, hqA⟩ hqF => by
    obtain ⟨c', hc', hc'y, hiff⟩ := h2 n Z hZ (qZ Z c)
    have hcc := qZ_inj_s hZ hc' hc hc'y; subst hcc
    exact hq (h0 q ⟨hqF.1.1, (hiff q.1 hqF.1.1).1 ⟨hqF.1.2, hqA.1⟩⟩)
  have hFib : IsClosed (Fib Z (qZ Z c)) :=
    (isClosed_Bz.inter (isClosed_singleton.preimage (continuous_qZ_s Z))).prod isClosed_univ
  obtain ⟨W, hWc, hWo, hKW, hWF⟩ := exists_isCompact_isOpen_between
    ((isCompact_support hf.1).inter_right ((h1 n Z hZ).prod isClosed_univ)) hFib.isOpen_compl hKF
  have hWcl : IsClopen W := ⟨hWc.isClosed, hWo⟩
  have hf2 := indicator_mul_mem (U := UU) hWcl.compl hf
  rw [show f = (fun q => W.indicator 1 q * f q) + (fun q => Wᶜ.indicator 1 q * f q) from funext fun q => by
    by_cases hq : q ∈ W <;> simp [hq], map_add,
    hs _ (indicator_mul_mem (U := Set.univ) hWcl ⟨hf.1, Set.subset_univ _⟩)
      (fun q hq => by simp [show q ∉ W from fun hqW => hWF hqW hq]),
    hk _ ⟨hf2.1, fun q hq => ⟨hf2.2 hq, fun hqZN =>
      (show q ∉ W from fun hqW => by simp [hqW] at hq) (hKW ⟨fun h => by simp [h] at hq, hqZN, Set.mem_univ _⟩)⟩⟩,
    add_zero]

theorem isClosed_GzS : IsClosed ((GzS Z : Subgroup (GLn k n)) : Set (GLn k n)) := BModbound.isClosed_Gz Z

private theorem isClosed_diff_of {D O : Set (Sp k n)} (hD : IsClosed D) (hO : O ⊆ UU)
    (h : IsClosed {u : (UU : Set (Sp k n)) | u.1 ∈ D \ O}) : IsClosed (D \ O) := by
  obtain ⟨F, hF, hFeq⟩ := isClosed_induced_iff.1 h
  refine isClosed_of_closure_subset fun x hx => ?_
  have hxD := closure_minimal Set.sdiff_subset hD hx
  by_contra hxn
  have hxU : x ∈ UU := hO (by_contra fun h' => hxn ⟨hxD, h'⟩)
  have hsub : D \ O ⊆ F ∪ UUᶜ := fun q hq => by
    by_cases hqU : q ∈ UU
    · exact Or.inl ((Set.ext_iff.1 hFeq ⟨q, hqU⟩).2 hq)
    · exact Or.inr hqU
  rcases closure_minimal hsub (hF.union isOpen_UU.isClosed_compl) hx with hxF | hxU'
  · exact hxn ((Set.ext_iff.1 hFeq ⟨x, hxU⟩).1 hxF)
  · exact hxU' hxU

theorem exists_open_orbit (T : Finset (Sp k n)) (hT : ∀ p ∈ T, p.2 ≠ 0) (D : Set (Sp k n)) (hD : IsClosed D)
    (hDinv : ∀ h ∈ Gz Z, ∀ q ∈ D, act h q ∈ D) (hcov : D ∩ UU ⊆ ⋃ p ∈ T, orb Z p) (hne : (D ∩ UU).Nonempty) :
    ∃ p₀ ∈ T, orb Z p₀ ⊆ D ∧ IsClosed (D \ orb Z p₀) := by
  let : MulAction (GzS Z) (UU : Set (Sp k n)) :=
    { smul := fun g q => ⟨act g.1 q.1, act_snd_ne_s g.1 q.2⟩
      one_smul := fun q => Subtype.ext (act_one q.1)
      mul_smul := fun g h q => Subtype.ext (act_mul g.1 h.1 q.1) }
  have : ContinuousSMul (GzS Z) (UU : Set (Sp k n)) := by
    have hgf : Continuous fun p : GzS Z × (UU : Set (Sp k n)) => (p.1 : GLn k n).val :=
      Units.continuous_val.comp (continuous_subtypeVal.comp continuous_fst)
    have hgi : Continuous fun p : GzS Z × (UU : Set (Sp k n)) => ((p.1 : GLn k n)⁻¹ : GLn k n).val :=
      Units.continuous_val.comp (continuous_inv.comp (continuous_subtypeVal.comp continuous_fst))
    have hq : Continuous fun p : GzS Z × (UU : Set (Sp k n)) => (p.2 : Sp k n) :=
      continuous_subtypeVal.comp continuous_snd
    exact ⟨(((hgf.matrix_mul (continuous_fst.comp hq)).matrix_mul hgi).prodMk
      (hgf.matrix_mulVec (continuous_snd.comp hq))).subtype_mk _⟩
  have : SigmaCompactSpace (GzS Z) := isClosed_GzS.sigmaCompactSpace
  have : LocallyCompactSpace (UU : Set (Sp k n)) := isOpen_UU.locallyCompactSpace
  obtain ⟨q₀, hq₀D, hq₀U⟩ := hne
  have orbit_eq : ∀ (u : (UU : Set (Sp k n))) (p : Sp k n), u.1 ∈ orb Z p →
      MulAction.orbit (GzS Z) u = {v : (UU : Set (Sp k n)) | v.1 ∈ orb Z p} := fun u p ⟨g, hg, hgu⟩ => Set.ext fun v =>
    ⟨fun ⟨h, hv⟩ => ⟨h.1 * g, (GzS Z).mul_mem h.2 hg, by rw [act_mul, hgu]; exact congrArg Subtype.val hv⟩,
     fun ⟨g', hg', hg'v⟩ => ⟨⟨g' * g⁻¹, (GzS Z).mul_mem hg' ((GzS Z).inv_mem hg)⟩, Subtype.ext <| by
      show act (g' * g⁻¹) u.1 = v.1; rw [← hgu, ← act_mul, mul_assoc, inv_mul_cancel, mul_one, hg'v]⟩⟩
  have hcov' : {u : (UU : Set (Sp k n)) | u.1 ∈ D} ⊆
      ⋃ x ∈ {u : (UU : Set (Sp k n)) | u.1 ∈ (T : Set (Sp k n))}, MulAction.orbit (GzS Z) x := fun u hu => by
    obtain ⟨p, hpT, hup⟩ := Set.mem_iUnion₂.1 (hcov ⟨hu, u.2⟩)
    exact Set.mem_iUnion₂.2 ⟨⟨p, hT p hpT⟩, hpT,
      by rw [orbit_eq ⟨p, hT p hpT⟩ p ⟨1, (GzS Z).one_mem, act_one p⟩]; exact hup⟩
  obtain ⟨x₀, hx₀, hcl⟩ := GroundTheory.Automorphic.ContragredientTranspose.exists_isClosed_diff_orbit
    (hD.preimage continuous_subtypeVal) ⟨⟨q₀, hq₀U⟩, hq₀D⟩ (fun (h : GzS Z) x hx => hDinv h.1 h.2 x.1 hx)
    (T.finite_toSet.preimage Subtype.val_injective.injOn).countable hcov'
  obtain ⟨p₀, hp₀T, g₀, hg₀, hg₀x⟩ := Set.mem_iUnion₂.1 (hcov ⟨hx₀, x₀.2⟩)
  refine ⟨p₀, hp₀T, fun q ⟨g, hg, hq⟩ => hq ▸ by
    rw [show act g p₀ = act (g * g₀⁻¹) x₀.1 by rw [← hg₀x, ← act_mul, mul_assoc, inv_mul_cancel, mul_one]]
    exact hDinv _ ((GzS Z).mul_mem hg ((GzS Z).inv_mem hg₀)) _ hx₀,
    isClosed_diff_of hD (orb_subset_UU (hT p₀ hp₀T))
      (by convert hcl using 1; ext u; simp [orbit_eq x₀ p₀ ⟨g₀, hg₀, hg₀x⟩])⟩

theorem main_ind [CharZero k] (h4 : StepMod (k := k)) (hZ : CR Z) (t : kˣ) (mm : Sp k n → ℂ) (s : Finset (Sp k n))
    (hs : ∀ p ∈ s, p.2 ≠ 0 ∧ ∃ (K L : Subgroup (GLn k n)) (g : GLn k n), g ∈ Gz Z ∧ act g p = sig Z t p ∧
      K ≤ GzS Z ∧ IsOpen (((↑) : GzS Z → GLn k n) ⁻¹' (K : Set (GLn k n))) ∧ IsCompact (K : Set (GLn k n)) ∧
      IsOpen (((↑) : GzS Z → GLn k n) ⁻¹' (L : Set (GLn k n))) ∧ L ≤ K ⊓ K.map (MulAut.conj g).toMonoidHom ∧
      L.Normal' K ∧ L.Normal' (K.map (MulAut.conj g).toMonoidHom) ∧ ((modul (stab Z p) K L g : ℝ) : ℂ) = mm p) :
    ∀ (N : ℕ) (T : Finset (Sp k n)), T.card ≤ N → T ⊆ s → ∀ D : Set (Sp k n), IsClosed D →
      (∀ h ∈ Gz Z, ∀ q ∈ D, act h q ∈ D) → (∀ q ∈ D, sig Z t q ∈ D) → D ∩ UU ⊆ ⋃ p ∈ T, orb Z p →
      ∀ ξ, Inv Z ξ → SuppU ξ D → ∀ Q : ℂ[X], (∏ p ∈ T, (X - Polynomial.C (mm p))) ∣ Q →
        Kills (aeval (pull Z t) Q ξ) UU := by
  classical
  intro N
  induction N with
  | zero =>
    intro T hT _ D _ _ _ hcov ξ _ hS Q _
    have hT0 := Finset.card_eq_zero.1 (Nat.le_zero.1 hT); subst hT0
    exact kills_aeval hZ t (kills_of_suppU (Set.eq_empty_of_forall_notMem fun _ hq => by simpa using hcov hq) hS) Q
  | succ N ih =>
    intro T hT hTs D hD hinv hsig hcov ξ hξ hS Q hQ
    by_cases hne : (D ∩ UU).Nonempty
    swap
    · exact kills_aeval hZ t (kills_of_suppU (Set.not_nonempty_iff_eq_empty.1 hne) hS) Q
    obtain ⟨p₀, hp₀T, hO, hcl⟩ := exists_open_orbit T (fun p hp => (hs p (hTs hp)).1) D hD hinv hcov hne
    obtain ⟨hp₀2, K, L, g, hg, hgp, hK, hKo, hKc, hLo, hLKK, hLn1, hLn2, hm⟩ := hs p₀ (hTs hp₀T)
    set O := orb Z p₀
    set U := (UU : Set (Sp k n)) ∩ (D \ O)ᶜ
    have hUD : U ∩ D = O := Set.ext fun q =>
      ⟨fun ⟨⟨_, hqn⟩, hqD⟩ => by_contra fun hqO => hqn ⟨hqD, hqO⟩,
       fun hqO => ⟨⟨orb_subset_UU hp₀2 hqO, fun h => h.2 hqO⟩, hO hqO⟩⟩
    have hstep := h4 n Z hZ t p₀ g hg hgp hp₀2 K hK hKo hKc L hLo hLKK hLn1 hLn2 D U hD
      (isOpen_UU.inter hcl.isOpen_compl) hUD hinv hsig ξ hξ hS
    rw [show D \ U = D \ O from Set.ext fun q =>
      ⟨fun ⟨hqD, hqU⟩ => ⟨hqD, fun hqO => hqU ⟨orb_subset_UU hp₀2 hqO, fun h => h.2 hqO⟩⟩,
       fun ⟨hqD, hqO⟩ => ⟨hqD, fun h => h.2 ⟨hqD, hqO⟩⟩⟩, hm] at hstep
    have hsig0 : sig Z t⁻¹ p₀ = act g⁻¹ p₀ := by
      have e1 : act g (sig Z t⁻¹ p₀) = p₀ := by rw [← sig_act_s Z t⁻¹ hg, hgp, sig_sig_s hZ]
      conv_rhs => rw [← e1]
      rw [← act_mul, inv_mul_cancel, act_one]
    set T' := T.filter fun p => orb Z p ≠ O
    have hT'sub : T' ⊆ T.erase p₀ := fun p hp =>
      Finset.mem_erase.2 ⟨fun h => (Finset.mem_filter.1 hp).2 (by rw [h]), (Finset.mem_filter.1 hp).1⟩
    obtain ⟨Q0, hQ0⟩ := hQ
    set R := (∏ p ∈ T.erase p₀, (X - Polynomial.C (mm p))) * Q0
    have key : aeval (pull Z t) Q ξ = aeval (pull Z t) R (pull Z t ξ - mm p₀ • ξ) := by
      rw [show Q = R * (X - Polynomial.C (mm p₀)) by rw [hQ0, ← Finset.mul_prod_erase T _ hp₀T]; ring,
        map_mul, Module.End.mul_eq_comp, LinearMap.comp_apply]; simp [Algebra.algebraMap_eq_smul_one]
    rw [key]
    refine ih T' (by have := Finset.card_le_card hT'sub; rw [Finset.card_erase_of_mem hp₀T] at this; omega)
      (fun p hp => hTs (Finset.mem_of_mem_filter p hp)) (D \ O) hcl
      (fun h hh q ⟨hqD, hqO⟩ => ⟨hinv h hh q hqD, fun ⟨g', hg', hg'q⟩ => hqO ⟨h⁻¹ * g',
        (GzS Z).mul_mem ((GzS Z).inv_mem hh) hg', by rw [act_mul, hg'q, ← act_mul, inv_mul_cancel, act_one]⟩⟩)
      (fun q ⟨hqD, hqO⟩ => ⟨hsig q hqD, fun ⟨g', hg', hg'q⟩ => hqO ⟨g' * g⁻¹,
        (GzS Z).mul_mem hg' ((GzS Z).inv_mem hg), by rw [act_mul, ← hsig0, ← sig_act_s Z t⁻¹ hg', hg'q, sig_sig_s hZ]⟩⟩)
      (fun q ⟨⟨hqD, hqO⟩, hqU⟩ => let ⟨p, hpT, hqp⟩ := Set.mem_iUnion₂.1 (hcov ⟨hqD, hqU⟩)
        Set.mem_iUnion₂.2 ⟨p, Finset.mem_filter.2 ⟨hpT, fun h => hqO (h ▸ hqp)⟩, hqp⟩)
      _ (fun g hg f hf => by simp [inv_pull hZ t hξ g hg f hf, hξ g hg f hf])
      hstep R (dvd_mul_of_dvd_left (Finset.prod_dvd_prod_of_subset _ _ _ hT'sub) Q0)

variable (k) in
theorem orbP_of [CharZero k] (h1 : ZNClosed (k := k)) (h2 : FibZN (k := k)) (h3 : Reps (k := k))
    (h4 : StepMod (k := k)) (h5 : ModBound (k := k)) : OrbP (k := k) := by
  classical
  intro n Z hZ hd t ht y
  obtain ⟨c, hc, hcy, -⟩ := h2 n Z hZ y
  obtain ⟨s, hs, hcov⟩ := h3 n Z hZ c hc
  have H : ∀ p ∈ s, ∃ a : ℝ, 2 * a < dB0 Z ∧ ∃ (K L : Subgroup (GLn k n)) (g : GLn k n),
      g ∈ Gz Z ∧ act g p = sig Z t p ∧ K ≤ GzS Z ∧ IsOpen (((↑) : GzS Z → GLn k n) ⁻¹' (K : Set (GLn k n))) ∧
      IsCompact (K : Set (GLn k n)) ∧ IsOpen (((↑) : GzS Z → GLn k n) ⁻¹' (L : Set (GLn k n))) ∧
      L ≤ K ⊓ K.map (MulAut.conj g).toMonoidHom ∧ L.Normal' K ∧ L.Normal' (K.map (MulAut.conj g).toMonoidHom) ∧
      modul (stab Z p) K L g = (nabs k t)⁻¹ ^ a := fun p hp => by
    obtain ⟨hp1, hpn, hp2, P, w, hgr, hpos⟩ := hs p hp
    obtain ⟨a, ha, hat⟩ := h5 n Z hZ hd c hc p P w hp1 hpn hp2 hgr hpos
    obtain ⟨K, L, g, hK, hKo, hKc, hLo, hLKK, hLn1, hLn2, hgval, hmod⟩ := hat t ht
    have hgr' := hgr t; simp only [← hgval] at hgr'
    obtain ⟨hgZ, hE, hv⟩ := hgr'
    have hgG : g ∈ Gz Z := hgZ
    have e2 : g.val * p.1 * g⁻¹.val = c + (t : k) • (p.1 - c) := by
      rw [show g.val * p.1 * g⁻¹.val = g.val * c * g⁻¹.val + g.val * (p.1 - c) * g⁻¹.val by
        rw [← add_mul, ← mul_add, add_sub_cancel], conj_mem_Z_shared hgG hc, hE, smul_mul_assoc, mul_assoc,
        Units.mul_inv, mul_one]
    exact ⟨a, ha, K, L, g, hgG, by rw [scaling_on_orbit_closure hZ hc t ⟨hp1, hpn⟩]; exact Prod.ext e2 hv,
      hK, hKo, hKc, hLo, hLKK, hLn1, hLn2, hmod⟩
  choose! a ha hKLg using H
  refine ⟨s.toList.map a, fun _ hx => let ⟨p, hp, hpx⟩ := List.mem_map.1 hx; hpx ▸ ha p (Finset.mem_toList.1 hp), ?_⟩
  intro ξ hsupp hinv hkill
  set mm : Sp k n → ℂ := fun p => (((nabs k t)⁻¹ ^ a p : ℝ) : ℂ)
  have hprod : (((s.toList.map a).map fun x => pull Z t - ((((nabs k t)⁻¹ : ℝ) ^ x : ℝ) : ℂ) • LinearMap.id).prod :
      Module.End ℂ (DistS k n)) = aeval (pull Z t) (∏ p ∈ s, (X - Polynomial.C (mm p))) := by
    rw [← Finset.prod_map_toList s (fun p => X - Polynomial.C (mm p)), map_list_prod, List.map_map, List.map_map]
    exact congrArg List.prod (List.map_congr_left fun p _ => by
      simp only [mm, Function.comp_apply, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]; rfl)
  rw [hprod]
  refine main_ind h4 hZ t mm s (fun p hp => let ⟨K, L, g, h⟩ := hKLg p hp; ⟨(hs p hp).2.2.1, K, L, g,
    h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.1, by rw [h.2.2.2.2.2.2.2.2.2]⟩)
    s.card s le_rfl subset_rfl (C0 Z c) (isClosed_C0 c)
    (fun _ hh _ hq => action_mem_orbit_closure hc hh hq) (fun _ hq => scaling_mem_orbit_closure hZ hc t hq)
    (fun q ⟨⟨hq1, hqn⟩, hqU⟩ => let ⟨p, hp, hqp⟩ := hcov q.1 hq1 hqn q.2 hqU; Set.mem_iUnion₂.2 ⟨p, hp, hqp⟩)
    ξ hinv (support_in_orbit_closure h1 h2 hZ hc (hcy ▸ hsupp) hkill) _ dvd_rfl

end PositivityTheory.RgUd.T.Nil.Orb.Oasm
end

section
open Matrix GroundTheory.Automorphic.Whittaker MulAction
open scoped Pointwise

namespace PositivityTheory.RgUd.T.Nil.Orb.BStep

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb

theorem count {G X : Type*} [Group G] [MulAction G X] (J A : Subgroup G) (hAJ : A ≤ J)
    (hn : ∀ j ∈ J, ∀ a ∈ A, j * a * j⁻¹ ∈ A) (y : X) :
    Nat.card ((fun j : G => j • ((fun a : G => a • y) '' (A : Set G))) '' (J : Set G)) *
      (A ⊓ MulAction.stabilizer G y).relIndex (J ⊓ MulAction.stabilizer G y) = A.relIndex J := by
  classical
  set P : Set X := (fun a : G => a • y) '' (A : Set G)
  set S := MulAction.stabilizer G y
  have himg : ((fun j : G => j • P) '' (J : Set G)) = MulAction.orbit J P :=
    Set.ext fun _ => ⟨fun ⟨j, hj, h⟩ => ⟨⟨j, hj⟩, h⟩, fun ⟨j, h⟩ => ⟨j, j.2, h⟩⟩
  have hAP : ∀ u ∈ A, u • P = P := fun u hu => Set.ext fun _ =>
    ⟨fun ⟨_, ⟨a, ha, h1⟩, h2⟩ => h2 ▸ h1 ▸ ⟨u * a, A.mul_mem hu ha, mul_smul u a y⟩,
     fun ⟨a, ha, h⟩ => h ▸ ⟨(u⁻¹ * a) • y, ⟨u⁻¹ * a, A.mul_mem (A.inv_mem hu) ha, rfl⟩, by simp [mul_smul]⟩⟩
  have hSP : ∀ s ∈ J, s ∈ S → s • P = P := fun s hsJ hsS => Set.ext fun _ =>
    ⟨fun ⟨_, ⟨a, ha, h1⟩, h2⟩ => h2 ▸ h1 ▸ ⟨s * a * s⁻¹, hn s hsJ a ha, by
        show (s * a * s⁻¹) • y = s • a • y; conv_lhs => rw [← (hsS : s • y = y)]; simp [mul_smul]⟩,
     fun ⟨a, ha, h⟩ => h ▸ ⟨(s⁻¹ * a * s) • y, ⟨_, by simpa using hn s⁻¹ (J.inv_mem hsJ) a ha, rfl⟩, by
        show s • (s⁻¹ * a * s) • y = a • y; rw [mul_smul, mul_smul, (hsS : s • y = y), smul_inv_smul]⟩⟩
  have hstab : MulAction.stabilizer J P = A.subgroupOf J ⊔ S.subgroupOf J := le_antisymm
    (fun u hu => by
      obtain ⟨a, ha, hay⟩ : (u : G) • y ∈ P :=
        (hu : (u : G) • P = P) ▸ Set.smul_mem_smul_set ⟨1, A.one_mem, one_smul G y⟩
      have hs : a⁻¹ * (u : G) ∈ S := by show (a⁻¹ * (u : G)) • y = y; rw [mul_smul, ← (hay : a • y = _), inv_smul_smul]
      rw [show u = (⟨a, hAJ ha⟩ : J) * ⟨a⁻¹ * u, J.mul_mem (J.inv_mem (hAJ ha)) u.2⟩ by ext; simp]
      exact Subgroup.mul_mem_sup ha hs)
    (sup_le (fun u hu => hAP u hu) (fun u hu => hSP u u.2 hu))
  have hnorm : (A.subgroupOf J).Normal := ⟨fun a ha g => by show ((g * a * g⁻¹ : J) : G) ∈ A; simpa using hn g g.2 a ha⟩
  have hcard : Nat.card ((fun j : G => j • P) '' (J : Set G)) = (A.subgroupOf J ⊔ S.subgroupOf J).index := by
    rw [himg, ← hstab, MulAction.index_stabilizer]; rfl
  have hb : (A ⊓ S).relIndex (J ⊓ S) = (A.subgroupOf J).relIndex (S.subgroupOf J) := by
    rw [← Subgroup.inf_subgroupOf_right S J, Subgroup.relIndex_subgroupOf inf_le_right]
    have h1 := Subgroup.relIndex_inf_mul_relIndex A S (J ⊓ S)
    rw [Subgroup.relIndex_eq_one.2 inf_le_right, mul_one] at h1
    rw [← h1, inf_of_le_right inf_le_right, inf_comm J S]
  have hm := Subgroup.relIndex_mul_index (le_sup_left : A.subgroupOf J ≤ A.subgroupOf J ⊔ S.subgroupOf J)
  rw [Subgroup.relIndex_sup_left] at hm; rw [hcard, hb, mul_comm, hm]; rfl

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem totDisc : TotallyDisconnectedSpace k := totallyDisconnectedSpace_localField

def SpT (k : Type) [Field k] (n : ℕ) : Type := Sp k n

instance : TopologicalSpace (SpT k n) := inferInstanceAs (TopologicalSpace (Sp k n))

theorem t2Sp : T2Space (SpT k n) := by
  have := GlobalTheory.SplitWeil.t2Space k
  have : T2Space (Mat k n) := inferInstanceAs (T2Space (Fin n → Fin n → k))
  exact inferInstanceAs (T2Space (Mat k n × (Fin n → k)))

theorem lcSp : LocallyCompactSpace (SpT k n) := by
  have : LocallyCompactSpace (Mat k n) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → k))
  exact inferInstanceAs (LocallyCompactSpace (Mat k n × (Fin n → k)))

theorem tdSp : TotallyDisconnectedSpace (SpT k n) := by
  have : TotallyDisconnectedSpace k := totDisc
  have : TotallyDisconnectedSpace (Mat k n) := inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → k))
  exact inferInstanceAs (TotallyDisconnectedSpace (Mat k n × (Fin n → k)))

instance actGL : MulAction (GLn k n) (SpT k n) where
  smul g p := (act g p : Sp k n)
  one_smul := act_one (k := k)
  mul_smul := act_mul (k := k)

theorem contSMul : ContinuousSMul (GLn k n) (SpT k n) := ⟨continuous_act_shared⟩

theorem isClosed_GzS (Z : SubM k n) : IsClosed (GzS Z : Set (GLn k n)) := Oasm.isClosed_GzS

theorem lcH (Z : SubM k n) : LocallyCompactSpace (GzS Z) :=
  (isClosed_GzS Z).isClosedEmbedding_subtypeVal.locallyCompactSpace

private theorem tdGL : TotallyDisconnectedSpace (GLn k n) := by
  have : TotallyDisconnectedSpace k := totDisc
  have : TotallyDisconnectedSpace (Mat k n) := inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → k))
  exact ⟨fun t _ ht x hx y hy => Units.val_injective
    (isTotallyDisconnected_of_totallyDisconnectedSpace (Units.val '' t) (Units.val '' t)
      subset_rfl (ht.image _ Units.continuous_val.continuousOn) ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩)⟩

theorem tdH (Z : SubM k n) : TotallyDisconnectedSpace (GzS Z) := by
  have := tdGL (k := k) (n := n); infer_instance

theorem scH (Z : SubM k n) : SigmaCompactSpace (GzS Z) := (isClosed_GzS Z).sigmaCompactSpace

theorem contSMulH (Z : SubM k n) : ContinuousSMul (GzS Z) (SpT k n) := by
  have := contSMul (k := k) (n := n)
  exact ⟨(continuous_subtypeVal.comp continuous_fst).smul continuous_snd⟩

theorem isOpen_UU : IsOpen (UU : Set (Sp k n)) := isOpen_UU_s

theorem relIndex_ne_zero {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] {J A : Subgroup H}
    (hJ : IsCompact (J : Set H)) (hA : IsOpen (A : Set H)) : A.relIndex J ≠ 0 := by
  let : SMul J (Set J) := ⟨fun g s => (fun x => g * x) '' s⟩
  have : CompactSpace J := isCompact_iff_compactSpace.mp hJ
  have hA' : IsOpen ((A.subgroupOf J : Subgroup J) : Set J) := by
    rw [Subgroup.coe_subgroupOf]; exact hA.preimage continuous_subtypeVal
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun g : J => g • ((A.subgroupOf J : Subgroup J) : Set J))
    (fun g => by rw [← Set.image_smul]; exact (Homeomorph.mulLeft g).isOpenMap _ hA')
    (fun x _ => Set.mem_iUnion.2 ⟨x, ⟨1, (A.subgroupOf J).one_mem, mul_one x⟩⟩)
  exact Subgroup.finiteIndex_iff.mp (Subgroup.finiteIndex_of_leftCoset_cover_const (Set.eq_univ_of_univ_subset ht))

attribute [local instance] t2Sp lcSp tdSp contSMul lcH tdH scH contSMulH

private theorem sig_act (Z : SubM k n) (t : kˣ) (h : GLn k n) (hh : h ∈ Gz Z) (q : Sp k n) :
    sig Z t (act h q) = act h (sig Z t q) := sig_act_s Z t hh q

theorem act_inv_act (h : GLn k n) (q : Sp k n) : act h⁻¹ (act h q) = q := by
  rw [← act_mul, inv_mul_cancel, act_one]

theorem act_snd_ne (h : GLn k n) {q : Sp k n} (hq : q.2 ≠ 0) : (act h q).2 ≠ 0 := act_snd_ne_s h hq

def toT (p : Sp k n) : SpT k n := p

theorem mem_orbit_iff' (Z : SubM k n) {p q : Sp k n} : toT q ∈ orbit (GzS Z) (toT p) ↔ q ∈ orb Z p :=
  ⟨fun ⟨g, hg⟩ => ⟨g, g.2, hg⟩, fun ⟨g, hg, hgq⟩ => ⟨⟨g, hg⟩, hgq⟩⟩

theorem lift_on_C' {U₁ C O : Set (Sp k n)} (hO : U₁ ∩ C = O) {P : Set (SpT k n)} (hP : ∀ x, toT x ∈ P → x ∈ O)
    {F : Sp k n → ℂ} (hF : F ∈ supportedIn U₁) (hFO : ∀ x ∈ O, F x = P.indicator 1 (toT x)) :
    ∀ x ∈ C, F x = P.indicator 1 (toT x) := fun x hx => by
  by_cases hxU : x ∈ U₁
  · exact hFO x (hO ▸ ⟨hxU, hx⟩)
  · rw [(by_contra fun hne => hxU ((mem_supportedIn.1 hF).2 hne) : F x = 0),
      Set.indicator_of_notMem fun hP' => hxU (hO.symm ▸ hP x hP').1]

theorem xi_eq {ξ : DistS k n} {C : Set (Sp k n)} (hξC : SuppU ξ C) {a b : Sp k n → ℂ}
    (ha : a ∈ supportedIn UU) (hb : b ∈ supportedIn UU) (h : ∀ q ∈ C, a q = b q) : ξ a = ξ b := by
  have := hξC (a - b) (Submodule.sub_mem _ ha hb) (fun q hq => by simp [h q hq]); rwa [map_sub, sub_eq_zero] at this

private theorem comp_sig_mem [CharZero k] (Z : SubM k n) (hZ : CR Z) (t : kˣ)
    {f : Sp k n → ℂ} (hf : f ∈ supportedIn UU) :
    (fun q => f (sig Z t q)) ∈ supportedIn UU :=
  ⟨⟨hf.1.1.comp_continuous (continuous_sig_s hZ t), hf.1.2.comp_homeomorph (sigH_s hZ t)⟩,
    fun q hq => @hf.2 (sig Z t q) hq⟩

theorem comp_act_memUU (h : GLn k n) {f : Sp k n → ℂ} (hf : f ∈ supportedIn UU) :
    (fun q => f (act h q)) ∈ supportedIn UU :=
  ⟨⟨hf.1.1.comp_continuous (actH_shared h).continuous, hf.1.2.comp_homeomorph (actH_shared h)⟩,
    fun q hq => act_inv_act h q ▸ act_snd_ne h⁻¹ (@hf.2 (act h q) hq)⟩

theorem relIndex_H (Z : SubM k n) (p : Sp k n) {K L : Subgroup (GLn k n)} (hKG : K ≤ GzS Z) :
    ((L ⊓ stab Z p).relIndex (K ⊓ stab Z p) = ((L.subgroupOf (GzS Z)) ⊓ stabilizer (GzS Z) (toT p)).relIndex
      ((K.subgroupOf (GzS Z)) ⊓ stabilizer (GzS Z) (toT p))) ∧
    L.relIndex K = (L.subgroupOf (GzS Z)).relIndex (K.subgroupOf (GzS Z)) := by
  have hst : (stab Z p).subgroupOf (GzS Z) = stabilizer (GzS Z) (toT p) :=
    Subgroup.ext fun x => ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
  have hinf : ∀ A B : Subgroup (GLn k n), (A ⊓ B).subgroupOf (GzS Z) = A.subgroupOf (GzS Z) ⊓ B.subgroupOf (GzS Z) :=
    fun _ _ => Subgroup.ext fun _ => Iff.rfl
  exact ⟨by rw [← hst, ← hinf, ← hinf, Subgroup.relIndex_subgroupOf (inf_le_left.trans hKG)],
    (Subgroup.relIndex_subgroupOf hKG).symm⟩

theorem isCompact_subgroupOf (Z : SubM k n) {K : Subgroup (GLn k n)} (hKG : K ≤ GzS Z)
    (hKc : IsCompact (K : Set (GLn k n))) :
    IsCompact ((K.subgroupOf (GzS Z) : Subgroup (GzS Z)) : Set (GzS Z)) := by
  rw [Subtype.isCompact_iff]; convert hKc using 1
  exact Set.ext fun x => ⟨fun ⟨_, hy, h⟩ => h ▸ hy, fun hx => ⟨⟨x, hKG hx⟩, hx, rfl⟩⟩

private theorem piece_count {n : ℕ} (Z : SubM k n) {ξ : DistS k n} (hξ : Inv Z ξ)
    {C U₁ : Set (Sp k n)} (hC : IsClosed C) (hU₁ : IsOpen U₁) (hU₁UU : U₁ ⊆ UU) {p : Sp k n}
    (hCinv : ∀ h ∈ Gz Z, ∀ q ∈ C, act h q ∈ C) (hO : U₁ ∩ C = orb Z p) (hξC : SuppU ξ C)
    {J A : Subgroup (GzS Z)} (hJc : IsCompact (J : Set (GzS Z))) (hAo : IsOpen (A : Set (GzS Z))) (hAJ : A ≤ J)
    (hn : ∀ j ∈ J, ∀ a ∈ A, j * a * j⁻¹ ∈ A) {fJ fA : Sp k n → ℂ} (hfJ : fJ ∈ supportedIn U₁)
    (hfA : fA ∈ supportedIn U₁) (hfJO : ∀ x ∈ orb Z p, fJ x = (orbitPiece J (toT p)).indicator 1 (toT x))
    (hfAO : ∀ x ∈ orb Z p, fA x = (orbitPiece A (toT p)).indicator 1 (toT x)) :
    ξ fJ * ((A ⊓ stabilizer (GzS Z) (toT p)).relIndex (J ⊓ stabilizer (GzS Z) (toT p)) : ℂ) =
      (A.relIndex J : ℂ) * ξ fA := by
  classical
  have hOorb : orbit (GzS Z) (toT p) = orb Z p := Set.ext fun q => mem_orbit_iff' Z (p := p) (q := q)
  have hOl : IsLocallyClosed (orbit (GzS Z) (toT p)) := ⟨U₁, C, hU₁, hC, (hOorb.symm ▸ hO).symm⟩
  obtain ⟨𝒮, -, h𝒮, hsum⟩ := exists_finset_orbitPiece (X := SpT k n) hOl hJc hAo hAJ hn (mem_orbit_self (toT p))
  choose! j hjJ hjS using h𝒮
  have hPsub : ∀ B : Subgroup (GzS Z), ∀ x, toT x ∈ orbitPiece B (toT p) → x ∈ orb Z p :=
    fun _ _ hx => (mem_orbit_iff' Z).1 (orbitPiece_subset_orbit (mem_orbit_self (toT p)) hx)
  have hfAUU : fA ∈ supportedIn UU := supportedIn_mono hU₁UU hfA
  have hsumξ : ξ fJ = ∑ S ∈ 𝒮, ξ (fun q => fA (act (((j S)⁻¹ : GzS Z) : GLn k n) q)) := by
    rw [← map_sum]
    refine xi_eq hξC (supportedIn_mono hU₁UU hfJ)
      (Submodule.sum_mem _ fun S _ => comp_act_memUU ((j S)⁻¹ : GzS Z).1 hfAUU) fun x hx => ?_
    rw [lift_on_C' hO (hPsub J) hfJ hfJO x hx, hsum (toT x), Finset.sum_apply]
    refine Finset.sum_congr rfl fun S hS => ?_
    rw [lift_on_C' hO (hPsub A) hfA hfAO _ (hCinv _ ((j S)⁻¹).2 x hx)]
    conv_lhs => rw [hjS S hS]
    by_cases hxS : toT (act (((j S)⁻¹ : GzS Z) : GLn k n) x) ∈ orbitPiece A (toT p)
    · rw [Set.indicator_of_mem (Set.mem_smul_set_iff_inv_smul_mem.2 (show (j S)⁻¹ • toT x ∈ _ from hxS)),
        Set.indicator_of_mem hxS]; rfl
    · rw [Set.indicator_of_notMem (fun h' => hxS (Set.mem_smul_set_iff_inv_smul_mem.1 h')), Set.indicator_of_notMem hxS]
  have hcard : ξ fJ = (𝒮.card : ℂ) * ξ fA := by
    rw [hsumξ, Finset.sum_congr rfl (fun S _ => hξ _ ((j S)⁻¹).2 fA (supportedIn_mono (Set.subset_univ _) hfA)),
      Finset.sum_const, nsmul_eq_mul]
  have hset : ((𝒮 : Set (Set (SpT k n)))) = (fun i : GzS Z => i • orbitPiece A (toT p)) '' (J : Set (GzS Z)) := by
    ext P; constructor
    · exact fun hP => ⟨j P, hjJ P hP, (hjS P hP).symm⟩
    · rintro ⟨i, hi, rfl⟩
      have h1 := hsum (i • toT p)
      have hiJ : i • toT p ∈ orbitPiece J (toT p) := ⟨i, hi, rfl⟩
      rw [Set.indicator_of_mem hiJ] at h1
      obtain ⟨S, hS, hiS⟩ : ∃ S ∈ 𝒮, i • toT p ∈ S := by
        by_contra hcon; push Not at hcon
        rw [Finset.sum_eq_zero fun S hS => Set.indicator_of_notMem (hcon S hS) _] at h1
        exact one_ne_zero h1
      have hsm : ∀ g ∈ J, g • orbitPiece A (toT p) = orbitPiece A (g • toT p) := fun g hg =>
        smul_orbitPiece (hn g hg) (fun a ha => by simpa using hn g⁻¹ (J.inv_mem hg) a ha) _
      have e2 : S = orbitPiece A (j S • toT p) := (hjS S hS).trans (hsm _ (hjJ S hS))
      show i • orbitPiece A (toT p) ∈ (𝒮 : Set (Set (SpT k n)))
      rw [Finset.mem_coe, hsm i hi, orbitPiece_eq_of_mem (e2 ▸ hiS), ← e2]; exact hS
  have hc := count J A hAJ hn (toT p)
  change Nat.card ((fun i : GzS Z => i • orbitPiece A (toT p)) '' (J : Set (GzS Z))) * _ = _ at hc
  rw [← hset, Nat.card_coe_set_eq, Set.ncard_coe_finset] at hc
  rw [hcard, mul_assoc, mul_comm (ξ fA), ← mul_assoc]
  exact_mod_cast congrArg (fun N : ℕ => (N : ℂ) * ξ fA) hc

theorem stepMod_pf (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [CharZero k] : StepMod (k := k) := by
  intro n Z hZ t p g hg hgp hp2 K hKG hKo hKc L hLo hLK hLn hLn' C U hC hU hUC hCinv hCsig ξ hξ hξC
  classical
  let gH : GzS Z := ⟨g, hg⟩
  set K' : Subgroup (GLn k n) := K.map (MulAut.conj g).toMonoidHom with hK'def
  have hK'G : K' ≤ GzS Z := fun _ ⟨_, hx, h⟩ => h ▸ (GzS Z).mul_mem ((GzS Z).mul_mem hg (hKG hx)) ((GzS Z).inv_mem hg)
  set KH := K.subgroupOf (GzS Z)
  set K'H := K'.subgroupOf (GzS Z)
  set LH := L.subgroupOf (GzS Z)
  have hKHc : IsCompact (KH : Set (GzS Z)) := isCompact_subgroupOf Z hKG hKc
  have hK'H : K'H = KH.map (MulAut.conj gH).toMonoidHom := Subgroup.ext fun x => by
    simp only [K'H, KH, Subgroup.mem_subgroupOf, Subgroup.mem_map, hK'def]
    exact ⟨fun ⟨y, hy, hyx⟩ => ⟨⟨y, hKG hy⟩, hy, Subtype.ext (by simpa [MulAut.conj_apply] using hyx)⟩,
      fun ⟨y, hy, h⟩ => h ▸ ⟨y, hy, by simp [MulAut.conj_apply, gH]⟩⟩
  have hK'Hco := hK'H ▸ isCompact_isOpen_map_conj hKHc hKo gH
  have hLKH : LH ≤ KH := fun _ hx => (hLK hx).1
  have hLK'H : LH ≤ K'H := fun _ hx => (hLK hx).2
  have hLHc : IsCompact (LH : Set (GzS Z)) := hKHc.of_isClosed_subset (LH.isClosed_of_isOpen hLo) hLKH
  let U₁ : Set (Sp k n) := {q | q.2 ≠ 0 ∧ ∃ h ∈ Gz Z, act h q ∈ U}
  have hU₁o : IsOpen U₁ := by
    have e : U₁ = UU ∩ ⋃ h : GzS Z, (fun q => act (h : GLn k n) q) ⁻¹' U := Set.ext fun q => by
      simp only [U₁, UU, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_preimage]
      exact ⟨fun ⟨h2, h, hh, hq⟩ => ⟨h2, ⟨h, hh⟩, hq⟩, fun ⟨h2, h, hq⟩ => ⟨h2, h.1, h.2, hq⟩⟩
    rw [e]
    exact isOpen_UU.inter (isOpen_iUnion fun h => hU.preimage
      (continuous_const_smul (h : GLn k n) : Continuous fun q : SpT k n => (h : GLn k n) • q))
  have hU₁UU : U₁ ⊆ UU := fun _ hq => hq.1
  have hU₁inv : ∀ h : GzS Z, ∀ x : SpT k n, x ∈ (U₁ : Set (SpT k n)) → h • x ∈ (U₁ : Set (SpT k n)) := by
    rintro h x ⟨hx2, h', hh', hx⟩
    let x' : Sp k n := x
    refine ⟨act_snd_ne (h : GLn k n) hx2, h' * (h : GLn k n)⁻¹, (GzS Z).mul_mem hh' ((GzS Z).inv_mem h.2), ?_⟩
    change act (h' * (h : GLn k n)⁻¹) (act (h : GLn k n) x') ∈ U
    rw [← act_mul, mul_assoc, inv_mul_cancel, mul_one]; exact hx
  have hO₁ : U₁ ∩ C = orb Z p := Set.ext fun q =>
    ⟨fun ⟨⟨_, h, hh, hqU⟩, hqC⟩ => by
      obtain ⟨g', hg', e⟩ := show act h q ∈ orb Z p from hUC ▸ ⟨hqU, hCinv h hh q hqC⟩
      exact ⟨h⁻¹ * g', (GzS Z).mul_mem ((GzS Z).inv_mem hh) hg',
        by rw [act_mul, e, ← act_mul, inv_mul_cancel, act_one]⟩,
    fun hq => by
      have hq' : q ∈ U ∩ C := hUC ▸ hq; obtain ⟨h, _, rfl⟩ := hq
      exact ⟨⟨act_snd_ne h hp2, 1, (GzS Z).one_mem, by rw [act_one]; exact hq'.1⟩, hq'.2⟩⟩
  have hOorb : orbit (GzS Z) (toT p) = orb Z p := Set.ext fun q => mem_orbit_iff' Z (p := p) (q := q)
  have hO₁' : ((U₁ : Set (SpT k n)) ∩ C) = orbit (GzS Z) (toT p) := hOorb.symm ▸ hO₁
  have hp0 : toT p ∈ orbit (GzS Z) (toT p) := mem_orbit_self (toT p)
  have hU₁oT : IsOpen (X := SpT k n) U₁ := hU₁o
  have hCT : IsClosed (X := SpT k n) C := hC
  have hKHo : IsOpen (KH : Set (GzS Z)) := hKo
  have hLHo : IsOpen (LH : Set (GzS Z)) := hLo
  have hlift : ∀ B : Subgroup (GzS Z), IsCompact (B : Set (GzS Z)) → IsOpen (B : Set (GzS Z)) →
      ∃ f ∈ supportedIn U₁, ∀ x ∈ orb Z p, f x = (orbitPiece B (toT p)).indicator 1 (toT x) := fun B hBc hBo => by
    obtain ⟨f, hf, hfO⟩ := exists_lift_orbit_piece (X := SpT k n) hU₁oT hCT hO₁' hBc hBo hp0
    exact ⟨f, hf, fun x hx => hfO (toT x) (hOorb ▸ hx)⟩
  obtain ⟨f₀, hf₀, hf₀O⟩ := hlift KH hKHc hKHo
  obtain ⟨f₁, hf₁, hf₁O⟩ := hlift K'H hK'Hco.1 hK'Hco.2
  obtain ⟨fL, hfL, hfLO⟩ := hlift LH hLHc hLHo
  have hPsub : ∀ B : Subgroup (GzS Z), ∀ x, toT x ∈ orbitPiece B (toT p) → x ∈ orb Z p :=
    fun _ _ hx => (mem_orbit_iff' Z).1 (orbitPiece_subset_orbit hp0 hx)
  set m : ℂ := ((modul (stab Z p) K L g : ℝ) : ℂ) with hm
  set ψ := pull Z t ξ - m • ξ
  have hψ : ∀ f, ψ f = ξ (fun q => f (sig Z t q)) - m * ξ f := fun _ => rfl
  have hV : ∀ v ∈ supportedIn UU, (∀ q ∈ C, v q = 0) → ψ v = 0 := fun v hv hvC => by
    rw [hψ, hξC v hv hvC, hξC _ (comp_sig_mem Z hZ t hv) (fun q hq => hvC _ (hCsig q hq))]; simp
  have hR : relSpan (X := SpT k n) (1 : GzS Z →* ℂ) U₁ ≤ LinearMap.ker ψ := Submodule.span_le.2 <| by
    rintro _ ⟨h, f, hf, rfl⟩
    simp only [MonoidHom.one_apply, one_smul]
    let f' : Sp k n → ℂ := f
    change ψ ((fun q : Sp k n => f' (act ((h⁻¹ : GzS Z) : GLn k n) q)) - f') = 0
    have e1 := hξ _ (h⁻¹).2 f' (supportedIn_mono (Set.subset_univ _) hf)
    have e2 : ξ (fun q => f' (act ((h⁻¹ : GzS Z) : GLn k n) (sig Z t q))) = ξ (fun q => f' (sig Z t q)) := by
      rw [← hξ _ (h⁻¹).2 (fun q => f' (sig Z t q))
        (supportedIn_mono (Set.subset_univ _) (comp_sig_mem Z hZ t (supportedIn_mono hU₁UU hf)))]
      congr 1; funext q; rw [sig_act Z t _ (h⁻¹).2]
    rw [ψ.map_sub, hψ, hψ, e1, e2, sub_self]
  have hsig_piece : ∀ q : Sp k n, toT (sig Z t q) ∈ orbitPiece KH (toT p) ↔
      toT (act g q) ∈ orbitPiece K'H (toT p) := fun q =>
    ⟨fun ⟨κ, hκ, e⟩ => by
      have hq : q = act ((κ : GLn k n) * g⁻¹) p := by
        have h1 : sig Z t (act ((κ : GLn k n) * g⁻¹) p) = sig Z t q := by
          rw [sig_act Z t _ ((GzS Z).mul_mem κ.2 ((GzS Z).inv_mem hg)), ← hgp, ← act_mul, inv_mul_cancel_right]; exact e
        have := congrArg (sig Z t⁻¹) h1; rw [sig_sig_s hZ, sig_sig_s hZ] at this; exact this.symm
      refine ⟨⟨g * (κ : GLn k n) * g⁻¹, hK'G ⟨κ, hκ, rfl⟩⟩, ⟨κ, hκ, rfl⟩, ?_⟩
      change act (g * (κ : GLn k n) * g⁻¹) p = act g q; rw [hq, ← act_mul, mul_assoc],
    fun ⟨κ', ⟨κ, hκ, hκe⟩, e⟩ => by
      have hκ' : (κ' : GLn k n) = g * κ * g⁻¹ := by simpa [MulAut.conj_apply] using hκe.symm
      have hq : q = act (κ * g⁻¹) p := by
        have := congrArg (act g⁻¹) (show act (κ' : GLn k n) p = act g q from e)
        rw [← act_mul, ← act_mul, inv_mul_cancel, act_one, hκ'] at this; rw [← this]; congr 1; group
      refine ⟨⟨κ, hKG hκ⟩, hκ, ?_⟩
      change act κ p = sig Z t q
      rw [hq, sig_act Z t _ ((GzS Z).mul_mem (hKG hκ) ((GzS Z).inv_mem hg)), ← hgp, ← act_mul, inv_mul_cancel_right]⟩
  have hX1 : ξ (fun q => f₀ (sig Z t q)) = ξ f₁ := by
    rw [← hξ g hg f₁ (supportedIn_mono (Set.subset_univ _) hf₁)]
    refine xi_eq hξC (comp_sig_mem Z hZ t (supportedIn_mono hU₁UU hf₀))
      (comp_act_memUU g (supportedIn_mono hU₁UU hf₁)) fun q hq => ?_
    rw [lift_on_C' hO₁ (hPsub KH) hf₀ hf₀O _ (hCsig q hq), lift_on_C' hO₁ (hPsub K'H) hf₁ hf₁O _ (hCinv g hg q hq)]
    by_cases h : toT (sig Z t q) ∈ orbitPiece KH (toT p)
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((hsig_piece q).1 h)]; rfl
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((hsig_piece q).2 h'))]
  have hc0 := piece_count Z hξ hC hU₁o hU₁UU hCinv hO₁ hξC hKHc hLHo hLKH
    (fun _ hj _ ha => hLn _ hj _ ha) hf₀ hfL hf₀O hfLO
  have hc1 := piece_count Z hξ hC hU₁o hU₁UU hCinv hO₁ hξC hK'Hco.1 hLHo hLK'H
    (fun _ hj _ ha => hLn' _ hj _ ha) hf₁ hfL hf₁O hfLO
  have ha0 := relIndex_ne_zero hKHc hLHo
  have ha1 := relIndex_ne_zero hK'Hco.1 hLHo
  have hb0 := right_ne_zero_of_mul ((count KH LH hLKH (fun _ hj _ ha => hLn _ hj _ ha) (toT p)).symm ▸ ha0)
  have hb1 := right_ne_zero_of_mul ((count K'H LH hLK'H (fun _ hj _ ha => hLn' _ hj _ ha) (toT p)).symm ▸ ha1)
  obtain ⟨r0, s0⟩ := relIndex_H Z p (L := L) hKG
  obtain ⟨r1, s1⟩ := relIndex_H Z p (L := L) hK'G
  have hmodul : modul (stab Z p) K L g =
      ((LH.relIndex K'H : ℝ) / ((LH ⊓ stabilizer (GzS Z) (toT p)).relIndex (K'H ⊓ stabilizer (GzS Z) (toT p)) : ℝ)) /
      ((LH.relIndex KH : ℝ) / ((LH ⊓ stabilizer (GzS Z) (toT p)).relIndex (KH ⊓ stabilizer (GzS Z) (toT p)) : ℝ)) := by
    rw [modul, ← hK'def, r0, s0, r1, s1]
  have hP : ψ f₀ = 0 := by
    rw [hψ, hX1, hm, hmodul]
    have ha0' : (LH.relIndex KH : ℂ) ≠ 0 := Nat.cast_ne_zero.2 ha0
    have ha1' : (LH.relIndex K'H : ℂ) ≠ 0 := Nat.cast_ne_zero.2 ha1
    have hb0' : ((LH ⊓ stabilizer (GzS Z) (toT p)).relIndex (KH ⊓ stabilizer (GzS Z) (toT p)) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.2 hb0
    have hb1' : ((LH ⊓ stabilizer (GzS Z) (toT p)).relIndex (K'H ⊓ stabilizer (GzS Z) (toT p)) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.2 hb1
    rw [eq_div_of_mul_eq hb0' hc0, eq_div_of_mul_eq hb1' hc1]
    push_cast; field_simp; ring
  have hle := supportedIn_le_of_base (X := SpT k n) hU₁oT hCT hO₁' hU₁inv (1 : GzS Z →* ℂ)
    (sup_le (relSpan_le_supportedIn _ hU₁inv) ((Submodule.span_singleton_le_iff_mem _ _).2 hf₀))
    le_sup_left KH hKHc hKHo (fun _ _ => rfl) f₀ (fun x hx => hf₀O x (hOorb ▸ hx))
    (Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self f₀)))
  have hker : supportedIn (X := SpT k n) U₁ ≤ LinearMap.ker ψ :=
    hle.trans (sup_le (sup_le hR ((Submodule.span_singleton_le_iff_mem _ _).2 hP))
      fun v hv => hV v (supportedIn_mono hU₁UU hv.1) hv.2)
  intro f hf hfCU
  have hKc' : IsCompact (X := SpT k n) (C ∩ Function.support f) := (isCompact_support hf.1).inter_left hC
  have hsub : C ∩ Function.support f ⊆ U₁ := fun q ⟨hqC, hqf⟩ => by
    have hq : q ∈ orb Z p := hUC ▸ ⟨by_contra fun h => hqf (hfCU q ⟨hqC, h⟩), hqC⟩
    rw [← hO₁] at hq; exact hq.1
  obtain ⟨B, hBc, hBo, hKB, hBU⟩ := exists_isCompact_isOpen_between (X := SpT k n) hKc' hU₁oT hsub
  set f₂ : Sp k n → ℂ := fun x => B.indicator 1 (toT x) * f x
  have hf₂ : f₂ ∈ supportedIn (X := SpT k n) U₁ :=
    ⟨(indicator_mul_mem (X := SpT k n) ⟨hBc.isClosed, hBo⟩ hf).1, fun x hx =>
      hBU (by_contra fun h => hx (show B.indicator 1 x * f x = 0 by rw [Set.indicator_of_notMem h, zero_mul]))⟩
  change ψ f = 0
  rw [show f = f₂ + (f - f₂) by abel, map_add, hker hf₂, zero_add]
  refine hV _ (Submodule.sub_mem _ hf (supportedIn_mono hU₁UU hf₂)) fun q hq => ?_
  by_cases hfq : f q = 0
  · simp [f₂, hfq]
  · change f q - B.indicator 1 (toT q) * f q = 0
    rw [Set.indicator_of_mem (hKB ⟨hq, hfq⟩ : toT q ∈ B), Pi.one_apply, one_mul, sub_self]

end PositivityTheory.RgUd.T.Nil.Orb.BStep
end

section
open Matrix GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.T.Nil

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil.BasePf

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem usage₁₀ [CharZero k] : BaseP (k := k) := by
  intro n Z hZ h0 ξ hS hI f hf
  have : TotallyDisconnectedSpace k := totallyDisconnectedSpace_localField
  have : LocallyCompactSpace (Mat k n) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → k))
  have : TotallyDisconnectedSpace (Mat k n) := inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → k))
  have : T2Space (Mat k n) := inferInstanceAs (T2Space (Fin n → Fin n → k))
  have hle : supportedIn {p : Sp k n | p.2 ≠ 0} ≤ LinearMap.ker ξ := supportedIn_le_of_local fun p hp => by
    obtain ⟨e, he, hee, hev, hprim⟩ := prim Z hZ.1 hZ.2 p.2 hp
    exact ⟨{q : Sp k n | e *ᵥ q.2 ≠ 0}, isOpen_ne_fun (continuous_const.matrix_mulVec continuous_snd) continuous_const,
      hev, fun g hg => LinearMap.mem_ker.2 (mainE Z hZ h0 e he hee hprim p.2 hev ξ hS hI g hg)⟩
  exact LinearMap.mem_ker.1 (hle hf)

theorem Asm.nilpB_of [CharZero k] (fourP : FourP (k := k)) (orbP : OrbP (k := k)) (locQ : LocQ (k := k))
    (baseP : BaseP (k := k)) : NilpB (k := k) := by
  intro n Z hCR hH
  by_cases hd : dB0 Z = 0
  · exact baseP n Z hCR hd
  refine locQ n Z hCR fun y ξ hξ hinv => ?_
  have hmono : ∀ η : DistS k n, Supp η (Fib Z y) → Supp η (Bz Z ×ˢ Set.univ) :=
    fun η hη f hf hvan => hη f hf fun p hp => hvan p ⟨hp.1.1, hp.2⟩
  obtain ⟨t, ht0, ht1⟩ := Asm.free_etale_sheaf_zmod_exists_hom_sending_generator k
  obtain ⟨𝓕, hF1, hF2, hF3, hF4, hF5, hF6⟩ := fourP n Z hCR
  obtain ⟨a, ha, hP⟩ := orbP n Z hCR (Nat.pos_of_ne_zero hd) t ht1 y
  have hξB := hmono ξ hξ
  have hFξ := hP (𝓕 ξ) (hF2 ξ y hξ) (hF3 ξ hξB hinv) (hH (𝓕 ξ) (hF1 ξ hξB) (hF3 ξ hξB hinv))
  have hξK := hP ξ hξ hinv (hH ξ hξB hinv)
  have key : ξ ∈ (supportedIn (UU : Set (Sp k n))).dualAnnihilator := by
    refine Asm.bez _ (pull Z t) (pull Z t⁻¹) (Asm.pull_inv Z hCR t).1 (Asm.pull_inv Z hCR t).2
      (fun m hm => (Submodule.mem_dualAnnihilator _).2
        (Asm.pull_kills Z hCR t m ((Submodule.mem_dualAnnihilator _).1 hm)))
      ((nabs k t)⁻¹) (one_lt_inv_iff₀.2 ⟨ht0, ht1⟩) (dB0 Z) a ha ξ ((Submodule.mem_dualAnnihilator _).2 hξK) ?_
    rw [Submodule.mem_dualAnnihilator]
    refine (hF4 _ (Asm.prod_supp Z hCR t _ a ξ hξB)).2 fun f hf => ?_
    rw [Asm.four_prod Z hCR 𝓕 hF1 hF5 hF6 t a ξ hξB f ⟨hf.1, Set.subset_univ _⟩]
    exact hFξ f hf
  exact (Submodule.mem_dualAnnihilator ξ).1 key

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem Orb.Ofib.fibZN [CharZero k] : Orb.FibZN (k := k) := by
  intro n Z hZ y
  obtain ⟨c, hc, hcy⟩ := qZ_surj_s hZ y
  refine ⟨c, hc, hcy, fun x hx => ⟨fun ⟨hqy, c', hc', hnil⟩ => ?_, fun hnil => ⟨?_, c, hc, hnil⟩⟩⟩
  · have hx' : x - c' ∈ Bz Z := fun a ha => by rw [mul_sub, sub_mul, hx a ha, hZ.1 a ha c' hc']
    have h1 : qZ Z x = qZ Z c' := sub_eq_zero.1 (by rw [← qZ_sub_s, qZ_nil_s Z hx' hnil])
    rwa [qZ_inj_s hZ hc' hc (by rw [← h1, hqy, hcy])] at hnil
  · have hx' : x - c ∈ Bz Z := fun a ha => by rw [mul_sub, sub_mul, hx a ha, hZ.1 a ha c hc]
    have h1 : qZ Z x = qZ Z c := sub_eq_zero.1 (by rw [← qZ_sub_s, qZ_nil_s Z hx' hnil])
    rw [h1, hcy]

theorem Orb.Final.orbP [CharZero k] : OrbP (k := k) :=
  Orb.Oasm.orbP_of k (Orb.Ozn.zNClosed (k := k)) (Orb.Ofib.fibZN k) (Orb.BReps.reps k)
    (Orb.BStep.stepMod_pf k) (Orb.BModbound.modBound k)

theorem Final.nilpB [CharZero k] : NilpB (k := k) :=
  Asm.nilpB_of k (Four.Final.fourP k) (Orb.Final.orbP k) (Four.Final.locQ k) (usage₁₀ k)

end PositivityTheory.RgUd.T.Nil
end
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.ModulusInduction =====
