module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.LocalToGlobal.ProjectiveLattices.GenSectA, Formalism.LocalToGlobal.ProjectiveLattices.GenSectB

-- ===== clump member: Formalism.LocalToGlobal.ProjectiveLattices.GenSectA =====
-- clump-header: {"m": "Formalism.LocalToGlobal.ProjectiveLattices.GenSectA", "h": "module\n\npublic import Mathlib.Algebra.MvPolynomial.PDeriv\npublic import Mathlib.RingTheory.Localization.FractionRing\npublic import Mathlib.RingTheory.Ideal.Maps\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace Formalism.L2.Pj.GenSect

open MvPolynomial
open scoped TensorProduct

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (D m : ℕ)

abbrev KT : Type := MvPolynomial (Fin (D + 1) × Fin m) K

abbrev KTf : Type := FractionRing (KT K D m)

abbrev ΩT : Type := MvPolynomial (Fin (D + 1) × Fin m) Ω

def ktToΩ : KT K D m →+* ΩT Ω D m := MvPolynomial.map (algebraMap K Ω)

def KTS : Submonoid (ΩT Ω D m) := (nonZeroDivisors (KT K D m)).map (ktToΩ K Ω D m)

abbrev RS : Type := Localization (KTS K Ω D m)

instance algKTR : Algebra (KTf K D m) (RS K Ω D m) :=
  (IsLocalization.map (M := nonZeroDivisors (KT K D m)) (T := KTS K Ω D m) (RS K Ω D m) (ktToΩ K Ω D m)
    (Submonoid.le_comap_map _) :
    KTf K D m →+* RS K Ω D m).toAlgebra

variable {K Ω D m}

def sec (x : Fin m → Ω) (i : Fin D) : ΩT Ω D m := ∑ j, X (i.succ, j) * C (x j)


variable (K) in
def Is (x : Fin m → Ω) : Ideal (RS K Ω D m) :=
  Ideal.span (Set.range fun i : Fin D => algebraMap (ΩT Ω D m) (RS K Ω D m) (sec x i))

def Zs (j₀ : Fin m) (p : Fin (D + 1) × Fin m) : Prop := p.1 ≠ 0 ∧ p.2 = j₀

instance (j₀ : Fin m) : DecidablePred (Zs (D := D) j₀) := fun p => by unfold Zs; infer_instance


variable (Ω D) in
abbrev CT (j₀ : Fin m) : Type :=
  MvPolynomial {p : Fin (D + 1) × Fin m // ¬ Zs j₀ p} Ω

def xv (j₀ : Fin m) (p : Fin (D + 1) × Fin m) : CT Ω D j₀ :=
  if h : Zs j₀ p then 0 else X ⟨p, h⟩

def rr (x : Fin m → Ω) (j₀ : Fin m) (j : Fin m) : Ω := x j / x j₀

def gs (x : Fin m → Ω) (j₀ : Fin m) (p : Fin (D + 1) × Fin m) : CT Ω D j₀ :=
  if Zs j₀ p then -∑ k, xv j₀ (p.1, k) * C (rr x j₀ k) else xv j₀ p

def psi (x : Fin m → Ω) (j₀ : Fin m) : ΩT Ω D m →ₐ[Ω] CT Ω D j₀ := aeval (gs x j₀)

def incl (j₀ : Fin m) : CT Ω D j₀ →ₐ[Ω] ΩT Ω D m := rename Subtype.val

theorem xv_of_not {j₀ : Fin m} {p : Fin (D + 1) × Fin m} (h : ¬ Zs j₀ p) :
    xv (Ω := Ω) j₀ p = X ⟨p, h⟩ := by
  first
  | (rw [xv, dite_eq_right h])

theorem xv_of_Z {j₀ : Fin m} {p : Fin (D + 1) × Fin m} (h : Zs j₀ p) :
    xv (Ω := Ω) j₀ p = 0 := by
  first
  | (rw [xv, dite_eq_left h])

theorem psi_X (x : Fin m → Ω) (j₀ : Fin m) (p : Fin (D + 1) × Fin m) :
    psi x j₀ (X p) = gs x j₀ p := by
  first
  | (rw [psi, aeval_X])

theorem psi_C (x : Fin m → Ω) (j₀ : Fin m) (a : Ω) :
    psi (D := D) x j₀ (C a) = C a := by
  first
  | (rw [psi, aeval_C, MvPolynomial.algebraMap_eq])

theorem incl_C (j₀ : Fin m) (a : Ω) : incl (D := D) j₀ (C a) = C a := by
  first
  | (rw [incl, rename_C])

theorem gs_succ (x : Fin m → Ω) (j₀ : Fin m) (i : Fin D) (j : Fin m) :
    gs x j₀ (i.succ, j) = xv j₀ (i.succ, j) +
      if j = j₀ then -∑ k, xv j₀ (i.succ, k) * C (rr x j₀ k) else 0 := by
  by_cases h : j = j₀
  · have hz : Zs j₀ (i.succ, j) := by
      unfold Zs
      exact ⟨Fin.succ_ne_zero i, h⟩
    rw [gs, ite_eq_left hz, xv_of_Z hz, ite_eq_left h, zero_add]
  · have hz : ¬ Zs j₀ (i.succ, j) := by
      unfold Zs
      exact fun hz => h hz.2
    rw [gs, ite_eq_right hz, ite_eq_right h, add_zero]

theorem psi_sec (x : Fin m → Ω) (j₀ : Fin m) (hx₀ : x j₀ ≠ 0) (i : Fin D) :
    psi x j₀ (sec x i) = 0 := by
  have hS : (∑ k, xv (Ω := Ω) j₀ (i.succ, k) * C (rr x j₀ k)) * C (x j₀) =
      ∑ k, xv (Ω := Ω) j₀ (i.succ, k) * C (x k) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc, ← C_mul, rr]
    congr 2
    exact div_mul_cancel₀ (x k) hx₀
  have hI : ∑ j : Fin m, (if j = j₀ then -∑ k, xv (Ω := Ω) j₀ (i.succ, k) * C (rr x j₀ k) else 0) * C (x j) =
      -(∑ k, xv (Ω := Ω) j₀ (i.succ, k) * C (rr x j₀ k)) * C (x j₀) := by
    rw [Finset.sum_eq_single j₀]
    · rw [ite_eq_left rfl]
    · intro b _ hb
      rw [ite_eq_right hb, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ j₀) h
  have h1 : psi x j₀ (sec x i) = ∑ j, gs x j₀ (i.succ, j) * C (x j) := by

    simp only [sec, map_sum, map_mul, psi_X, psi_C]
  rw [h1]
  simp only [gs_succ, add_mul]
  rw [Finset.sum_add_distrib, hI, neg_mul, hS]
  first
  | exact add_neg_cancel _
  | abel

theorem incl_xv_succ (j₀ : Fin m) (i : Fin D) (k : Fin m) :
    incl (Ω := Ω) j₀ (xv j₀ (i.succ, k)) = if k = j₀ then 0 else X (i.succ, k) := by
  by_cases h : k = j₀
  · have hz : Zs j₀ (i.succ, k) := by
      unfold Zs
      exact ⟨Fin.succ_ne_zero i, h⟩
    rw [xv_of_Z hz, map_zero, ite_eq_left h]
  · have hz : ¬ Zs j₀ (i.succ, k) := by
      unfold Zs
      exact fun hz => h hz.2
    rw [xv_of_not hz, ite_eq_right h, incl, rename_X]

theorem X_sub_incl_gs (x : Fin m → Ω) (j₀ : Fin m) (hx₀ : x j₀ ≠ 0) (i : Fin D) :
    X (i.succ, j₀) - incl j₀ (gs x j₀ (i.succ, j₀)) = C (x j₀)⁻¹ * sec x i := by
  have hz : Zs j₀ (i.succ, j₀) := by
    unfold Zs
    exact ⟨Fin.succ_ne_zero i, rfl⟩
  rw [gs, ite_eq_left hz]

  simp only [map_neg, map_sum, map_mul, incl_C, incl_xv_succ, sub_neg_eq_add, sec, Finset.mul_sum]
  have hX : (X (i.succ, j₀) : ΩT Ω D m) = ∑ j : Fin m, if j = j₀ then (X (i.succ, j₀) : ΩT Ω D m) else 0 := by
    simp
  rw [hX, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : j = j₀
  · subst h
    rw [ite_eq_left rfl, ite_eq_left rfl, zero_mul, add_zero, mul_left_comm, ← C_mul, inv_mul_cancel₀ hx₀, C_1, mul_one]
  · rw [ite_eq_right h, ite_eq_right h, zero_add, rr, div_eq_mul_inv, C_mul]
    ring

theorem sub_incl_psi_mem (x : Fin m → Ω) (j₀ : Fin m) (hx₀ : x j₀ ≠ 0) (f : ΩT Ω D m) :
    f - incl j₀ (psi x j₀ f) ∈ Ideal.span (Set.range (sec x)) := by
  have hgen : ∀ p : Fin (D + 1) × Fin m,
      X p - incl j₀ (psi x j₀ (X p)) ∈ Ideal.span (Set.range (sec x)) := by
    intro p
    rw [psi_X]
    by_cases hp : Zs j₀ p
    · obtain ⟨i', j⟩ := p
      have hp' : i' ≠ 0 ∧ j = j₀ := hp
      obtain ⟨i, rfl⟩ : ∃ i : Fin D, i.succ = i' := by
        first
        | exact Fin.exists_succ_eq.mpr hp'.1
      rw [hp'.2, X_sub_incl_gs x j₀ hx₀ i]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
    · first
      | (rw [gs, ite_eq_right hp, xv_of_not hp, incl, rename_X, sub_self]
         exact Ideal.zero_mem _)
  induction f using MvPolynomial.induction_on
  next a =>
    rw [psi_C, incl_C, sub_self]
    exact Ideal.zero_mem _
  next f g hf hg =>
    have e : f + g - incl j₀ (psi x j₀ (f + g)) =
        (f - incl j₀ (psi x j₀ f)) + (g - incl j₀ (psi x j₀ g)) := by
      simp only [map_add (f := _)]
      ring
    rw [e]
    exact Ideal.add_mem _ hf hg
  next f p hf =>
    have e : f * X p - incl j₀ (psi x j₀ (f * X p)) =
        (f - incl j₀ (psi x j₀ f)) * X p + incl j₀ (psi x j₀ f) * (X p - incl j₀ (psi x j₀ (X p))) := by
      simp only [map_mul]
      ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hf) (Ideal.mul_mem_left _ _ (hgen p))

theorem psi_eq_zero_iff (x : Fin m → Ω) (j₀ : Fin m) (hx₀ : x j₀ ≠ 0) (f : ΩT Ω D m) :
    psi x j₀ f = 0 ↔ f ∈ Ideal.span (Set.range (sec x)) := by
  constructor
  · intro h
    have hm := sub_incl_psi_mem x j₀ hx₀ f
    rwa [h, map_zero, sub_zero] at hm
  · intro hf
    have hle : Ideal.span (Set.range (sec (D := D) x)) ≤ RingHom.ker (psi (D := D) x j₀) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact RingHom.mem_ker.mpr (psi_sec x j₀ hx₀ i)
    exact RingHom.mem_ker.mp (hle hf)

theorem pderiv_xv (j₀ : Fin m) (q : {p : Fin (D + 1) × Fin m // ¬ Zs j₀ p}) (p : Fin (D + 1) × Fin m) :
    pderiv q (xv (Ω := Ω) j₀ p) = if p = q.1 then 1 else 0 := by
  by_cases hp : Zs j₀ p
  · have hne : p ≠ q.1 := fun h => q.2 (h ▸ hp)
    rw [xv_of_Z hp, map_zero, ite_eq_right hne]
  · rw [xv_of_not hp, pderiv_X, Pi.single_apply]
    by_cases h : p = q.1
    · have e : (⟨p, hp⟩ : {p : Fin (D + 1) × Fin m // ¬ Zs j₀ p}) = q := Subtype.ext h
      rw [ite_eq_left e, ite_eq_left h]
    · have e : (⟨p, hp⟩ : {p : Fin (D + 1) × Fin m // ¬ Zs j₀ p}) ≠ q :=
        fun e => h (congrArg Subtype.val e)
      rw [ite_eq_right e, ite_eq_right h]

theorem pderiv_gs (x : Fin m → Ω) (j₀ : Fin m) (q : {p : Fin (D + 1) × Fin m // ¬ Zs j₀ p})
    (p : Fin (D + 1) × Fin m) :
    pderiv q (gs x j₀ p) = (if p = q.1 then 1 else 0) -
      if Zs j₀ p ∧ p.1 = q.1.1 then C (rr x j₀ q.1.2) else 0 := by
  by_cases hp : Zs j₀ p
  · have hne : p ≠ q.1 := fun h => q.2 (h ▸ hp)
    rw [gs, ite_eq_left hp, ite_eq_right hne, zero_sub, map_neg]
    congr 1

    simp only [map_sum, Derivation.leibniz, pderiv_C, smul_eq_mul, pderiv_xv, mul_zero, zero_add]
    rw [Finset.sum_eq_single q.1.2]
    · by_cases h1 : p.1 = q.1.1
      · have e : (p.1, q.1.2) = q.1 := Prod.ext h1 rfl
        rw [ite_eq_left e, ite_eq_left ⟨hp, h1⟩, mul_one]
      · have e : (p.1, q.1.2) ≠ q.1 := fun h => h1 (by have h' := congrArg Prod.fst h; exact h')
        have hn : ¬ (Zs j₀ p ∧ p.1 = q.1.1) := fun h => h1 h.2
        rw [ite_eq_right e, ite_eq_right hn, mul_zero]
    · intro k _ hk
      have e : (p.1, k) ≠ q.1 := fun h => hk (congrArg Prod.snd h)
      rw [ite_eq_right e, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · have hn : ¬ (Zs j₀ p ∧ p.1 = q.1.1) := fun h => hp h.1
    rw [gs, ite_eq_right hp, pderiv_xv, ite_eq_right hn, sub_zero]

theorem pderiv_aeval {ι : Type*} [Fintype ι] [DecidableEq ι] (j₀ : Fin m) (u : ι → CT Ω D j₀)
    (q : {p : Fin (D + 1) × Fin m // ¬ Zs j₀ p}) (G : MvPolynomial ι K) :
    pderiv q (aeval u G) = ∑ p, aeval u (pderiv p G) * pderiv q (u p) := by
  induction G using MvPolynomial.induction_on
  next a =>
    first
    | (rw [aeval_C, MvPolynomial.algebraMap_apply, pderiv_C]
       simp only [pderiv_C, map_zero, zero_mul, Finset.sum_const_zero])
  next G₁ G₂ h₁ h₂ =>
    simp only [map_add (f := _), h₁, h₂, add_mul, Finset.sum_add_distrib]
  next G i h =>
    have e1 : ∀ p, pderiv p (G * X i) = G * pderiv p (X i) + X i * pderiv p G := fun p => by
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    have hs : ∑ p, aeval u (G * pderiv p (X i)) * pderiv q (u p) = aeval u G * pderiv q (u i) := by
      rw [Finset.sum_eq_single i]
      · rw [pderiv_X_self, mul_one]
      · intro b _ hb
        have h0 : pderiv b (X i : MvPolynomial ι K) = 0 := by
          first
          | exact pderiv_X_of_ne (Ne.symm hb)
        rw [h0, mul_zero, map_zero, zero_mul]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    rw [map_mul, aeval_X, Derivation.leibniz, smul_eq_mul, smul_eq_mul, h]
    simp only [e1, map_add (f := _), add_mul, Finset.sum_add_distrib]
    rw [hs]
    simp only [map_mul, aeval_X, Finset.mul_sum, mul_assoc]

end Formalism.L2.Pj.GenSect
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.ProjectiveLattices.GenSectA =====

-- ===== clump member: Formalism.LocalToGlobal.ProjectiveLattices.GenSectB =====
-- clump-header: {"m": "Formalism.LocalToGlobal.ProjectiveLattices.GenSectB", "h": "module\n\npublic import Formalism.LocalToGlobal.ProjectiveLattices.GenSectA\npublic import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure\npublic import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace Formalism.L2.Pj.GenSect

open MvPolynomial Cardinal

open MvPolynomial in
theorem exists_pderiv_ne_zero_lt' {K : Type*} [Field K] [CharZero K] {ι : Type*}
    (P : MvPolynomial ι K) (hP : 0 < P.totalDegree) :
    ∃ i, pderiv i P ≠ 0 ∧ (pderiv i P).totalDegree < P.totalDegree := by
  classical
  have hP0 : P ≠ 0 := by
    rintro rfl
    simp at hP
  obtain ⟨s, hs, hsd⟩ := Finset.exists_mem_eq_sup P.support (support_nonempty.2 hP0)
    (fun s : ι →₀ ℕ => s.sum fun _ e => e)
  have htd : P.totalDegree = s.sum fun _ e => e := hsd
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [htd] at hP
    simp at hP
  obtain ⟨i, hi⟩ : ∃ i, s i ≠ 0 := by
    by_contra h
    push Not at h
    exact hs0 (Finsupp.ext h)
  have hdeg : ∀ t : ι →₀ ℕ, t i ≠ 0 →
      (t.sum fun _ e => e) = ((t - Finsupp.single i 1).sum fun _ e => e) + 1 := by
    intro t ht
    have hle : Finsupp.single i 1 ≤ t := Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 ht)
    conv_lhs => rw [← tsub_add_cancel_of_le hle]
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
  have hder : pderiv i P =
      ∑ t ∈ P.support, monomial (t - Finsupp.single i 1) (AddMonoidAlgebra.coeff P t * (t i : K)) := by
    conv_lhs => rw [P.as_sum]

    rw [map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [pderiv_monomial]
  refine ⟨i, ?_, ?_⟩
  · intro h0
    have hc := congrArg (AddMonoidAlgebra.coeff · (s - Finsupp.single i 1)) h0
    rw [hder, coeff_sum, AddMonoidAlgebra.coeff_zero, Finset.sum_eq_single s] at hc
    · rw [coeff_monomial, ite_eq_left rfl] at hc
      exact mul_ne_zero (mem_support_iff.1 hs) (by exact_mod_cast hi) hc
    · intro t _ hts
      rw [coeff_monomial]
      split_ifs with heq
      · by_cases hti : t i = 0
        · simp [hti]
        · exfalso
          apply hts
          have h1 : Finsupp.single i 1 ≤ t := Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hti)
          have h2 : Finsupp.single i 1 ≤ s := Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hi)
          rw [← tsub_add_cancel_of_le h1, ← tsub_add_cancel_of_le h2, heq]
      · rfl
    · intro hns
      exact absurd hs hns
  · have hpos : (⊥ : ℕ) < s.sum fun _ e => e := by
      rw [← htd]
      exact hP
    rw [htd, hder]
    refine lt_of_le_of_lt (MvPolynomial.totalDegree_finsetSum _ _) ((Finset.sup_lt_iff hpos).2 fun t ht => ?_)
    by_cases hti : t i = 0
    · simpa [hti, htd] using hP
    · refine lt_of_le_of_lt (totalDegree_monomial_le _ _) ?_
      have h1 := hdeg t hti
      have h2 : (t.sum fun _ e => e) ≤ s.sum fun _ e => e := by
        rw [← htd]
        exact le_totalDegree ht
      rw [h1] at h2
      exact h2

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D m : ℕ}

theorem card_Z (j₀ : Fin m) : Fintype.card {p : Fin (D + 1) × Fin m // Zs j₀ p} = D := by
  let e : {p : Fin (D + 1) × Fin m // Zs j₀ p} ≃ {i : Fin (D + 1) // i ≠ 0} :=
    { toFun := fun q => ⟨q.1.1, (q.2 : q.1.1 ≠ 0 ∧ q.1.2 = j₀).1⟩
      invFun := fun i => ⟨(i.1, j₀), (⟨i.2, rfl⟩ : i.1 ≠ 0 ∧ j₀ = j₀)⟩
      left_inv := fun q => by
        obtain ⟨⟨a, b⟩, h⟩ := q
        have hb : b = j₀ := (h : a ≠ 0 ∧ b = j₀).2
        subst hb
        rfl
      right_inv := fun i => rfl }
  rw [Fintype.card_congr e, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq]
  simp

theorem trdeg_CT (j₀ : Fin m) (htr : Algebra.trdeg K Ω = D) :
    Algebra.trdeg K (CT (Ω := Ω) (D := D) j₀) = (Fintype.card (Fin (D + 1) × Fin m) : Cardinal) := by
  classical
  have hle : D ≤ Fintype.card (Fin (D + 1) × Fin m) := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    exact (Nat.le_succ D).trans (Nat.le_mul_of_pos_right _ j₀.pos)
  rw [← trdeg_add_eq (R := K) (S := Ω) (A := CT (Ω := Ω) (D := D) j₀), htr,
    MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, Cardinal.mk_fintype,
    Fintype.card_subtype_compl, card_Z, ← Nat.cast_add, Nat.add_sub_of_le hle]

theorem isAlgebraic_map_adjoin {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (φ : A →ₐ[R] B) (hφ : Function.Injective φ) (s : Set A) {a : A}
    (h : IsAlgebraic (Algebra.adjoin R s) a) : IsAlgebraic (Algebra.adjoin R (φ '' s)) (φ a) := by
  have hmem : ∀ y : Algebra.adjoin R s, φ y ∈ Algebra.adjoin R (φ '' s) := by
    intro y
    rw [← AlgHom.map_adjoin]
    exact Subalgebra.mem_map.2 ⟨y, y.2, rfl⟩
  let f : Algebra.adjoin R s →+* Algebra.adjoin R (φ '' s) :=
    ((φ.comp (Algebra.adjoin R s).val).codRestrict _ hmem).toRingHom
  have hf : Function.Injective f := fun y z hyz => Subtype.ext (hφ (congrArg Subtype.val hyz))
  exact h.ringHom_of_comp_eq (f := f) (g := φ.toRingHom) hf (RingHom.ext fun y => rfl)

theorem alg_CT (x : Fin m → Ω) (j₀ : Fin m)
    (halg : ∀ ω : Ω, IsAlgebraic (Algebra.adjoin K (Set.range (rr x j₀))) ω)
    (hr : ∀ k, IsAlgebraic (Algebra.adjoin K (Set.range (gs (D := D) x j₀)))
      (C (rr x j₀ k) : CT (Ω := Ω) (D := D) j₀)) :
    Algebra.IsAlgebraic (Algebra.adjoin K (Set.range (gs (D := D) x j₀))) (CT (Ω := Ω) (D := D) j₀) := by
  have hC : ∀ ω : Ω, IsAlgebraic (Algebra.adjoin K (Set.range (gs (D := D) x j₀)))
      (C ω : CT (Ω := Ω) (D := D) j₀) := by
    intro ω
    have h1 := isAlgebraic_map_adjoin (IsScalarTower.toAlgHom K Ω (CT (Ω := Ω) (D := D) j₀)) (C_injective _ _) _
      (halg ω)
    refine IsAlgebraic.adjoin_of_forall_isAlgebraic ?_ h1
    rintro _ ⟨⟨_, ⟨k, rfl⟩, rfl⟩, -⟩
    exact hr k
  constructor
  intro c
  have hc : c ∈ Algebra.adjoin K (Set.range (X : _ → CT (Ω := Ω) (D := D) j₀) ∪ Set.range (C : Ω → CT (Ω := Ω) (D := D) j₀)) := by
    induction c using MvPolynomial.induction_on with
    | C a => exact Algebra.subset_adjoin (Or.inr ⟨a, rfl⟩)
    | add p r hp hr => exact add_mem hp hr
    | mul_X p n hp => exact mul_mem hp (Algebra.subset_adjoin (Or.inl ⟨n, rfl⟩))
  have h0 : IsAlgebraic (Algebra.adjoin K (Set.range (X : _ → CT (Ω := Ω) (D := D) j₀) ∪
      Set.range (C : Ω → CT (Ω := Ω) (D := D) j₀))) c :=
    isAlgebraic_algebraMap (⟨c, hc⟩ : Algebra.adjoin K _)
  refine IsAlgebraic.adjoin_of_forall_isAlgebraic ?_ h0
  rintro y ⟨hy | ⟨ω, rfl⟩, -⟩
  · obtain ⟨q, rfl⟩ := hy
    have hq : (X q : CT (Ω := Ω) (D := D) j₀) ∈ Algebra.adjoin K (Set.range (gs (D := D) x j₀)) :=
      Algebra.subset_adjoin ⟨q.1, by rw [gs, ite_eq_right q.2, xv_of_not q.2]⟩
    exact isAlgebraic_algebraMap (⟨X q, hq⟩ : Algebra.adjoin K _)
  · exact hC ω

theorem gs_indep [CharZero K] (x : Fin m → Ω) (j₀ : Fin m) (hx₀ : x j₀ ≠ 0)
    (htr : Algebra.trdeg K Ω = D)
    (halg : ∀ ω : Ω, IsAlgebraic (Algebra.adjoin K (Set.range (rr x j₀))) ω) :
    AlgebraicIndependent K (gs (D := D) x j₀) := by
  classical
  by_contra hdep
  have hex : ∃ n, ∃ G : MvPolynomial (Fin (D + 1) × Fin m) K, aeval (gs x j₀) G = 0 ∧ G ≠ 0 ∧
      G.totalDegree = n := by
    rw [algebraicIndependent_iff] at hdep
    push Not at hdep
    obtain ⟨G, h1, h2⟩ := hdep
    exact ⟨_, G, h1, h2, rfl⟩
  obtain ⟨G, hG0, hGne, hGdeg⟩ := Nat.find_spec hex
  have hmin : ∀ H : MvPolynomial (Fin (D + 1) × Fin m) K, H.totalDegree < G.totalDegree →
      aeval (gs x j₀) H = 0 → H = 0 := by
    intro H hH h0
    by_contra hne
    rw [hGdeg] at hH
    exact Nat.find_min hex hH ⟨H, h0, hne, rfl⟩
  have hd : ∀ q : {p : Fin (D + 1) × Fin m // ¬ Zs j₀ p},
      ∑ p, aeval (gs x j₀) (pderiv p G) * pderiv q (gs x j₀ p) = 0 := by
    intro q; rw [← pderiv_aeval, hG0, map_zero]
  have hsum : ∀ q : {p : Fin (D + 1) × Fin m // ¬ Zs j₀ p},
      ∑ p, aeval (gs x j₀) (pderiv p G) * pderiv q (gs x j₀ p) =
        aeval (gs x j₀) (pderiv q.1 G) -
          if q.1.1 = 0 then 0 else aeval (gs x j₀) (pderiv (q.1.1, j₀) G) * C (rr x j₀ q.1.2) := by
    intro q
    simp_rw [pderiv_gs, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    congr 1
    split_ifs with h0
    · exact Finset.sum_eq_zero fun p _ =>
        ite_eq_right (show ¬ (Zs j₀ p ∧ p.1 = q.1.1) from fun e => e.1.1 (e.2.trans h0))
    · rw [Finset.sum_eq_single (q.1.1, j₀)]
      · exact ite_eq_left (show Zs j₀ (q.1.1, j₀) ∧ (q.1.1, j₀).1 = q.1.1 from ⟨⟨h0, rfl⟩, rfl⟩)
      · intro p _ hp
        exact ite_eq_right (show ¬ (Zs j₀ p ∧ p.1 = q.1.1) from fun e => hp (Prod.ext_iff.mpr ⟨e.2, e.1.2⟩))
      · intro h; exact absurd (Finset.mem_univ _) h
  have hpos : 0 < G.totalDegree := by
    by_contra h
    have h0 : G.totalDegree = 0 := by omega
    rw [totalDegree_eq_zero_iff_eq_C] at h0
    rw [h0, aeval_C] at hG0
    have hc : AddMonoidAlgebra.coeff G 0 = 0 :=
      (algebraMap K (CT (Ω := Ω) (D := D) j₀)).injective (by rw [hG0, map_zero])
    exact hGne (by rw [h0, hc, C_0])
  obtain ⟨p₁, hp₁ne, hp₁lt⟩ := exists_pderiv_ne_zero_lt' G hpos
  have hp₁ : aeval (gs x j₀) (pderiv p₁ G) ≠ 0 := fun h => hp₁ne (hmin _ hp₁lt h)
  have hexi : ∃ i : Fin D, aeval (gs x j₀) (pderiv (i.succ, j₀) G) ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hp₁
    by_cases hZ : Zs j₀ p₁
    · obtain ⟨h1, h2⟩ := hZ
      obtain ⟨i, hi⟩ := Fin.exists_succ_eq.mpr h1
      have e : p₁ = (i.succ, j₀) := Prod.ext_iff.mpr ⟨hi.symm, h2⟩
      rw [e]; exact hall i
    · have h := hd ⟨p₁, hZ⟩
      rw [hsum] at h
      split_ifs at h with h0
      · rwa [sub_zero] at h
      · obtain ⟨i, hi⟩ := Fin.exists_succ_eq.mpr h0
        simp only at h hi
        rw [← hi, hall i, zero_mul, sub_zero] at h
        exact h
  obtain ⟨i, hi⟩ := hexi
  have hr : ∀ k, IsAlgebraic (Algebra.adjoin K (Set.range (gs (D := D) x j₀)))
      (C (rr x j₀ k) : CT (Ω := Ω) (D := D) j₀) := by
    intro k
    by_cases hk : k = j₀
    · subst hk
      rw [rr, div_self hx₀, C_1]
      exact isAlgebraic_one
    · have hq : ¬ Zs j₀ (i.succ, k) := fun h => hk h.2
      have h := hd ⟨(i.succ, k), hq⟩
      rw [hsum, ite_eq_right (Fin.succ_ne_zero i), sub_eq_zero] at h
      have m1 : aeval (gs x j₀) (pderiv (i.succ, j₀) G) ∈ Algebra.adjoin K (Set.range (gs x j₀)) := by
        rw [Algebra.adjoin_range_eq_range_aeval]; exact ⟨_, rfl⟩
      have m2 : aeval (gs x j₀) (pderiv (i.succ, k) G) ∈ Algebra.adjoin K (Set.range (gs x j₀)) := by
        rw [Algebra.adjoin_range_eq_range_aeval]; exact ⟨_, rfl⟩
      refine ⟨Polynomial.C ⟨_, m1⟩ * Polynomial.X - Polynomial.C ⟨_, m2⟩, ?_, ?_⟩
      · intro h0
        have h1 := congrArg (fun f => _root_.AddMonoidAlgebra.coeff (M := ℕ) f 1) h0
        simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C,
          Polynomial.coeff_zero, ite_eq_left, one_ne_zero, ite_false, sub_zero] at h1
        exact hi (congrArg Subtype.val h1)
      · rw [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_C, Polynomial.aeval_X]
        exact sub_eq_zero.mpr h.symm
  have := alg_CT x j₀ halg hr
  have htb : IsTranscendenceBasis K (gs (D := D) x j₀) :=
    Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite K (gs x j₀)
      (by rw [trdeg_CT j₀ htr, Cardinal.mk_fintype])
  exact hdep htb.1

theorem gs_alg [CharZero K] (x : Fin m → Ω) (j₀ : Fin m) (hx₀ : x j₀ ≠ 0)
    (htr : Algebra.trdeg K Ω = D)
    (halg : ∀ ω : Ω, IsAlgebraic (Algebra.adjoin K (Set.range (rr x j₀))) ω) :
    Algebra.IsAlgebraic (Algebra.adjoin K (Set.range (gs (D := D) x j₀))) (CT (Ω := Ω) (D := D) j₀) :=
  ((gs_indep x j₀ hx₀ htr halg).isTranscendenceBasis_of_trdeg_le_of_finite
    (by rw [trdeg_CT j₀ htr, Cardinal.mk_fintype])).isAlgebraic

theorem halg_of (x : Fin m → Ω) (j₀ : Fin m) (htr : Algebra.trdeg K Ω = D)
    (hbig : Algebra.trdeg K (IntermediateField.adjoin K (Set.range fun j => x j / x j₀)) = D) :
    ∀ ω : Ω, IsAlgebraic (Algebra.adjoin K (Set.range (rr x j₀))) ω := by
  intro ω
  have hadd := trdeg_add_eq (R := K)
    (S := IntermediateField.adjoin K (Set.range fun j => x j / x j₀)) (A := Ω)
  rw [hbig, htr] at hadd
  have h0 : Algebra.trdeg (IntermediateField.adjoin K (Set.range fun j => x j / x j₀)) Ω = 0 := by
    rcases (Cardinal.add_eq_left_iff).mp hadd with h | h
    · exact absurd ((le_max_left _ _).trans h) (not_le.mpr ((Cardinal.natCast_lt_aleph0 (n := D))))
    · exact h
  have halg : Algebra.IsAlgebraic (IntermediateField.adjoin K (Set.range fun j => x j / x j₀)) Ω := by
    first
    | exact trdeg_eq_zero_iff.mp h0
  exact IntermediateField.isAlgebraic_adjoin_iff.mp (halg.isAlgebraic ω)

end Formalism.L2.Pj.GenSect
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.ProjectiveLattices.GenSectB =====
