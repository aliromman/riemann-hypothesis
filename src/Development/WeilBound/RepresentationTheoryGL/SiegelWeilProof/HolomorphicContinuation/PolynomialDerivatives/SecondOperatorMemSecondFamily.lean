module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.PartialDerivZeroSecondFamily
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.XPderivMono
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.CoeffSmulX
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.ContractionFirstOperatorAdjoint
import Std.Tactic.BVDecide.Normalize.Bool

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.FunctionalRepresentationByContraction, Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.SecondOperatorMemSecondFamily

-- ===== clump member: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.FunctionalRepresentationByContraction =====
-- clump-header: {"m": "Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.FunctionalRepresentationByContraction", "h": "module\n\npublic import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.PartialDerivZeroSecondFamily\nimport Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.CoeffSmulX\npublic import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.XPderivMono\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open MvPolynomial Finsupp

namespace PositivityTheory.Rg.Sw.LC

namespace CoreC

open PositivityTheory.Rg.Sw G

variable {m n : ℕ}

def cand (ε : Fin m → Bool) (r : Fin m → ℕ) : Finset (Fin m × Fin n × Bool →₀ ℕ) :=
  ((Fintype.piFinset fun _ : Fin m × Fin n × Bool => Finset.range (∑ a, r a + 1)).image
    Finsupp.equivFunOnFinite.symm).filter (fun t => (∀ k ∈ t.support, inF1 ε k) ∧ rdeg ε t = r)

theorem le_rdeg (ε : Fin m → Bool) (t : Fin m × Fin n × Bool →₀ ℕ) (k) (hk : inF1 ε k) : t k ≤ rdeg ε t k.1 := by
  obtain ⟨a, i, b⟩ := k
  simp only [inF1] at hk
  subst hk
  unfold rdeg
  exact Finset.single_le_sum (f := fun i' => t (a, i', !ε a)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

theorem mem_cand (ε : Fin m → Bool) (r : Fin m → ℕ) (t : Fin m × Fin n × Bool →₀ ℕ) :
    t ∈ cand ε r ↔ (∀ k ∈ t.support, inF1 ε k) ∧ rdeg ε t = r := by
  unfold cand
  rw [Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  rw [Finset.mem_image]
  refine ⟨⇑t, ?_, by simp⟩
  rw [Fintype.mem_piFinset]
  intro k
  rw [Finset.mem_range, Nat.lt_succ_iff]
  by_cases hk : inF1 ε k
  · calc t k ≤ rdeg ε t k.1 := le_rdeg ε t k hk
      _ = r k.1 := by rw [h.2]
      _ ≤ ∑ a, r a := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
  · have : t k = 0 := by
      by_contra h0; exact hk (h.1 k (Finsupp.mem_support_iff.mpr h0))
    rw [this]; exact Nat.zero_le _

def Bm (ε : Fin m → Bool) (c : ℝ) (Λ : PX m n →ₗ[ℂ] ℂ) (s : Fin m × Fin n × Bool →₀ ℕ) : PX m n :=
  if ∀ k ∈ s.support, inF1 ε k then
    ∑ t ∈ cand ε (rdeg ε s), (Λ (monomial s 1 * monomial (t.mapDomain pE) 1) / (wt c t : ℂ)) • monomial t 1
  else 0

def Bop (ε : Fin m → Bool) (c : ℝ) (Λ : PX m n →ₗ[ℂ] ℂ) : Module.End ℂ (PX m n) :=
  (MvPolynomial.basisMonomials (Fin m × Fin n × Bool) ℂ).constr ℂ (Bm ε c Λ)

theorem Bop_mono (ε : Fin m → Bool) (c : ℝ) (Λ : PX m n →ₗ[ℂ] ℂ) (s : Fin m × Fin n × Bool →₀ ℕ) :
    Bop ε c Λ (monomial s 1) = Bm ε c Λ s := by
  have := (MvPolynomial.basisMonomials (Fin m × Fin n × Bool) ℂ).constr_basis ℂ (Bm ε c Λ) s
  rwa [MvPolynomial.coe_basisMonomials] at this

theorem as_sum' (p : PX m n) : p = ∑ s ∈ p.support, p.coeff s • monomial s (1 : ℂ) := by
  conv_lhs => rw [p.as_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [smul_monomial, smul_eq_mul, mul_one]

theorem monomial_mem_first_family (ε : Fin m → Bool) {t : Fin m × Fin n × Bool →₀ ℕ} (ht : ∀ k ∈ t.support, inF1 ε k) (d : ℂ) :
    (monomial t d : PX m n) ∈ F1 ε := by
  rw [mem_first_family_iff]
  intro s hs
  have : s = t := by
    by_contra h; exact (MvPolynomial.mem_support_iff.mp hs) (by rw [coeff_monomial, ite_eq_right (Ne.symm h)])
  subst this; exact ht

theorem monomial_mem_second_family (ε : Fin m → Bool) {t : Fin m × Fin n × Bool →₀ ℕ} (ht : ∀ k ∈ t.support, ¬ inF1 ε k) (d : ℂ) :
    (monomial t d : PX m n) ∈ F2 ε := by
  rw [mem_second_family_iff]
  intro s hs
  have : s = t := by
    by_contra h; exact (MvPolynomial.mem_support_iff.mp hs) (by rw [coeff_monomial, ite_eq_right (Ne.symm h)])
  subst this; exact ht

theorem representing_monomial_mem_first_family (ε : Fin m → Bool) (c : ℝ) (Λ : PX m n →ₗ[ℂ] ℂ) (s) : Bm ε c Λ s ∈ F1 ε := by
  unfold Bm
  split_ifs
  · exact Submodule.sum_mem _ fun t ht => Submodule.smul_mem _ _ (monomial_mem_first_family ε ((mem_cand ε _ t).mp ht).1 1)
  · exact Submodule.zero_mem _

theorem representing_operator_mem_first_family (ε : Fin m → Bool) (c : ℝ) (Λ : PX m n →ₗ[ℂ] ℂ) (p : PX m n) : Bop ε c Λ p ∈ F1 ε := by

  rw [as_sum' p, map_sum]
  exact Submodule.sum_mem _ fun s _ => by rw [map_smul, Bop_mono]; exact Submodule.smul_mem _ _ (representing_monomial_mem_first_family ε c Λ s)

theorem mapDomain_pE_pE (u : Fin m × Fin n × Bool →₀ ℕ) : (u.mapDomain pE).mapDomain pE = u := by
  rw [← Finsupp.mapDomain_comp]
  have h : (pE : Fin m × Fin n × Bool → Fin m × Fin n × Bool) ∘ pE = id := by
    funext k
    exact pE_pE k
  rw [h, Finsupp.mapDomain_id]

theorem partner_support_first_family (ε : Fin m → Bool) {u : Fin m × Fin n × Bool →₀ ℕ} (hu : ∀ k ∈ u.support, ¬ inF1 ε k) :
    ∀ k ∈ (u.mapDomain pE).support, inF1 ε k := by
  intro k hk
  rw [Finsupp.mem_support_iff, Finsupp.mapDomain_equiv_apply, pE_symm] at hk
  have := hu (pE k) (Finsupp.mem_support_iff.mpr hk)
  rwa [first_family_partner_iff, not_not] at this

theorem partner_support_second_family (ε : Fin m → Bool) {u : Fin m × Fin n × Bool →₀ ℕ} (hu : ∀ k ∈ u.support, inF1 ε k) :
    ∀ k ∈ (u.mapDomain pE).support, ¬ inF1 ε k := by
  intro k hk
  rw [Finsupp.mem_support_iff, Finsupp.mapDomain_equiv_apply, pE_symm] at hk
  have := hu (pE k) (Finsupp.mem_support_iff.mpr hk)
  rwa [first_family_partner_iff] at this

theorem key_mono (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) (Λ : PX m n →ₗ[ℂ] ℂ) (hΛ : ∀ a b p, Λ (Dop ε c a b p) = 0)
    {s u : Fin m × Fin n × Bool →₀ ℕ} (hs : ∀ k ∈ s.support, inF1 ε k) (hu : ∀ k ∈ u.support, ¬ inF1 ε k) :
    Λ (monomial s 1 * monomial u 1) = contr c (Bm ε c Λ s * monomial u 1) := by
  unfold Bm
  rw [ite_eq_left hs, Finset.sum_mul, contr_sum]
  simp_rw [smul_mul_assoc, contr_smul]
  have e : ∀ t ∈ cand ε (rdeg ε s), contr c (monomial t 1 * monomial u 1) =
      if t = u.mapDomain pE then (wt c t : ℂ) else 0 := fun t ht => by
    rw [contr_mono ε c ((mem_cand ε _ t).mp ht).1 hu]; simp
  rw [Finset.sum_congr rfl fun t ht => by rw [e t ht]]
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with hmem
  · rw [mapDomain_pE_pE, div_mul_cancel₀]
    exact_mod_cast (wt_pos hc _).ne'
  · refine centre ε c Λ hΛ hs hu fun h => hmem ?_
    rw [mem_cand]; exact ⟨partner_support_first_family ε hu, h.symm⟩

theorem functional_representation_by_contraction (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) (Λ : PX m n →ₗ[ℂ] ℂ) (hΛ : ∀ a b p, Λ (Dop ε c a b p) = 0)
    {f g : PX m n} (hf : f ∈ F1 ε) (hg : g ∈ F2 ε) : Λ (f * g) = contr c (Bop ε c Λ f * g) := by

  conv_lhs => rw [as_sum' f, as_sum' g, Finset.sum_mul_sum, map_sum]

  conv_rhs => rw [as_sum' f, map_sum, as_sum' g, Finset.sum_mul_sum, contr_sum]
  refine Finset.sum_congr rfl fun s hs => ?_

  rw [map_sum, contr_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [map_smul, Bop_mono, smul_mul_smul_comm, map_smul, smul_mul_smul_comm, contr_smul,
    key_mono ε hc Λ hΛ ((mem_first_family_iff ε f).mp hf s hs) ((mem_second_family_iff ε g).mp hg u hu), smul_eq_mul]

end CoreC

end PositivityTheory.Rg.Sw.LC
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.FunctionalRepresentationByContraction =====

-- ===== clump member: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.SecondOperatorMemSecondFamily =====
-- clump-header: {"m": "Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.SecondOperatorMemSecondFamily", "h": "module\n\npublic import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.FunctionalRepresentationByContraction\nimport Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.CoeffSmulX\npublic import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.ContractionFirstOperatorAdjoint\nimport Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.XPderivMono\nimport Std.Tactic.BVDecide.Normalize.Bool\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open MvPolynomial Finsupp

namespace PositivityTheory.Rg.Sw.LC

namespace CoreC

open PositivityTheory.Rg.Sw G

variable {m n : ℕ}

theorem first_operator_mem_first_family (ε : Fin m → Bool) (c : ℝ) (a b : Fin m) {f : PX m n} (hf : f ∈ F1 ε) : D1 ε c a b f ∈ F1 ε := by
  unfold D1
  split_ifs with hab ha ha
  · refine (F1 ε).neg_mem ((F1 ε).sum_mem fun i _ => variable_mul_mem_first_family ε (by simp [inF1, ha]) (partial_deriv_mem_first_family ε _ hf))
  · exact (F1 ε).sum_mem fun i _ => variable_mul_mem_first_family ε (by simp [inF1, ← hab]; simpa using ha) (partial_deriv_mem_first_family ε _ hf)
  · have hb : ε b = false := by cases h' : ε b <;> simp_all
    refine (F1 ε).smul_mem _ ((F1 ε).sum_mem fun i _ => ?_)
    rw [mul_assoc]
    exact variable_mul_mem_first_family ε (by simp [inF1, ha]) (variable_mul_mem_first_family ε (by simp [inF1, hb]) hf)
  · have hb : ε b = true := by cases h' : ε b <;> simp_all
    exact (F1 ε).smul_mem _ ((F1 ε).sum_mem fun i _ => partial_deriv_mem_first_family ε _ (partial_deriv_mem_first_family ε _ hf))

theorem second_operator_mem_second_family (ε : Fin m → Bool) (c : ℝ) (a b : Fin m) {g : PX m n} (hg : g ∈ F2 ε) : D2 ε c a b g ∈ F2 ε := by
  unfold D2
  split_ifs with hab ha ha
  · exact (F2 ε).sum_mem fun i _ => variable_mul_mem_second_family ε (by simp [inF1, ← hab, ha]) (partial_deriv_mem_second_family ε _ hg)
  · refine (F2 ε).neg_mem ((F2 ε).sum_mem fun i _ => variable_mul_mem_second_family ε (by simp [inF1]; simpa using ha)
      (partial_deriv_mem_second_family ε _ hg))
  · exact (F2 ε).smul_mem _ ((F2 ε).sum_mem fun i _ => partial_deriv_mem_second_family ε _ (partial_deriv_mem_second_family ε _ hg))
  · have hb : ε b = true := by cases h' : ε b <;> simp_all
    refine (F2 ε).smul_mem _ ((F2 ε).sum_mem fun i _ => ?_)
    rw [mul_assoc]
    exact variable_mul_mem_second_family ε (by simp [inF1]; simpa using ha) (variable_mul_mem_second_family ε (by simp [inF1, hb]) hg)

theorem bf_mono_right (w : (Fin m × Fin n × Bool →₀ ℕ) → ℂ) (p : PX m n) (t : Fin m × Fin n × Bool →₀ ℕ) :
    bf w p (monomial t 1) = p.coeff t * w t := by
  classical
  rw [bf_eq w (p.support ∪ {t}) Finset.subset_union_left ((support_monomial_subset).trans Finset.subset_union_right)]
  rw [Finset.sum_eq_single t]
  · simp [coeff_monomial]
  · intro s _ hs; simp [coeff_monomial, Ne.symm hs]
  · intro h; simp [coeff_monomial]; left; by_contra h'; exact h (Finset.mem_union_left _
      (MvPolynomial.mem_support_iff.mpr h'))

theorem nondeg (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) {h : PX m n} (hh : h ∈ F1 ε)
    (h0 : ∀ u : Fin m × Fin n × Bool →₀ ℕ, (∀ k ∈ u.support, ¬ inF1 ε k) → contr c (h * monomial u 1) = 0) : h = 0 := by
  ext s
  change h.coeff s = 0
  by_cases hs : ∀ k ∈ s.support, inF1 ε k
  · have hu := partner_support_second_family ε hs
    have := h0 (s.mapDomain pE) hu
    rw [contr_eq_bf ε c hh (monomial_mem_second_family ε hu 1), rename_monomial, mapDomain_pE_pE, bf_mono_right] at this
    exact (mul_eq_zero.mp this).resolve_right (by exact_mod_cast (wt_pos hc s).ne')
  · by_contra hne
    exact hs ((mem_first_family_iff ε h).mp hh s (MvPolynomial.mem_support_iff.mpr hne))

theorem Bop_box (ε : Fin m → Bool) (c : ℝ) (Λ : PX m n →ₗ[ℂ] ℂ) (R : Set (Fin m → ℕ)) :
    ∀ f ∈ box (n := n) ε R, Bop ε c Λ f ∈ box ε R := by
  intro f hf
  refine Submodule.span_induction (p := fun x _ => Bop ε c Λ x ∈ box ε R) ?_ ?_ ?_ ?_ hf
  · rintro x ⟨s, hs, hR, rfl⟩
    rw [Bop_mono]
    unfold Bm
    rw [ite_eq_left hs]
    refine Submodule.sum_mem _ fun t ht => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    obtain ⟨htF, htr⟩ := (mem_cand ε _ t).mp ht
    exact ⟨t, htF, by rw [htr]; exact hR, rfl⟩
  · simp
  · intro x y _ _ hx hy; rw [map_add]; exact add_mem hx hy
  · intro r x _ hx; rw [map_smul]; exact Submodule.smul_mem _ r hx

end CoreC

open CoreC in
theorem repB : RepB := by
  intro m n ε c hc Λ hΛ
  refine ⟨Bop ε c Λ, fun R f hf => Bop_box ε c Λ R f hf, fun f hf g hg => functional_representation_by_contraction ε hc Λ hΛ hf hg, ?_⟩
  intro a b f hf
  have hB1 : Bop ε c Λ (D1 ε c a b f) ∈ F1 ε := representing_operator_mem_first_family ε c Λ _
  have hB2 : D1 ε c a b (Bop ε c Λ f) ∈ F1 ε := first_operator_mem_first_family ε c a b (representing_operator_mem_first_family ε c Λ f)
  rw [← sub_eq_zero]
  refine nondeg ε hc (Submodule.sub_mem _ hB1 hB2) fun u hu => ?_
  have hg : (monomial u (1 : ℂ) : PX m n) ∈ F2 ε := monomial_mem_second_family ε hu 1
  rw [sub_mul, contr_sub, ← functional_representation_by_contraction ε hc Λ hΛ (first_operator_mem_first_family ε c a b hf) hg,
    contraction_first_operator_adjoint ε hc a b (representing_operator_mem_first_family ε c Λ f) hg, ← functional_representation_by_contraction ε hc Λ hΛ hf (second_operator_mem_second_family ε c a b hg), sub_neg_eq_add,
    ← map_add, ← dop_split ε c a b hf hg, hΛ]

end PositivityTheory.Rg.Sw.LC
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.SecondOperatorMemSecondFamily =====
