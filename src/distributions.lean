import data.real.basic
import algebra.big_operators.finprod
import .external_lemmas

open set set.finite

open_locale classical big_operators

structure fspm (Ω : Type*) :=
(pr : Ω → ℝ)
(finite : (function.support pr).finite)
(nonneg : ∀ x, 0 ≤ pr x)
(normal : ∑ᶠ x, pr x = 1)

variables {Ω : Type*} (σ : fspm Ω)

namespace fspm

def support : set Ω := function.support σ.pr

lemma nmem_support (x : Ω) : x ∉ σ.support ↔ σ.pr x = 0 := function.nmem_support

lemma mem_support (x : Ω) : x ∈ σ.support ↔ σ.pr x ≠ 0 := function.mem_support

lemma support_finite : σ.support.finite := σ.finite

lemma support_of_set_finite (A : set Ω) : (A ∩ σ.support).finite := 
inter_of_right σ.support_finite _

lemma le_one_of_mem_support {x : Ω} (h : x ∈ σ.support) : σ.pr x ≤ 1 :=
  le_trans (single_le_finsum _ σ.support_finite σ.nonneg) (le_of_eq σ.normal)

lemma le_one_of_nmem_support {x : Ω} (h : x ∉ σ.support) : σ.pr x ≤ 1 :=
  le_trans (le_of_eq ((σ.nmem_support _).mp h)) zero_le_one

lemma pr_le_one (x : Ω) : σ.pr x ≤ 1 := dite (x ∈ σ.support) (σ.le_one_of_mem_support) (σ.le_one_of_nmem_support)

noncomputable def Pr (A : set Ω) : ℝ := ∑ᶠ x ∈ A, σ.pr x

lemma Pr_eq (A : set Ω) : σ.Pr A = ∑ᶠ x ∈ A, σ.pr x := rfl

lemma Pr_singleton (x : Ω) : σ.Pr {x} = σ.pr x := finsum_mem_singleton

lemma Pr_sum_singletons (A : set Ω) : ∑ᶠ x ∈ A, σ.Pr {x} = σ.Pr A :=
  by simp only [Pr_eq, finsum_mem_congr, Pr_singleton]

lemma Pr_nonneg (A : set Ω) : 0 ≤ σ.Pr A := 
begin 
  rw Pr, apply finsum_mem_nonneg,
  exact (λ _ _, σ.nonneg _)
end

lemma Pr_normal : σ.Pr univ = 1 := 
begin
  rw [Pr, finsum_mem_univ],
  exact σ.normal
end

lemma Pr_additive {A B : set Ω} (h: disjoint A B) : σ.Pr (A ∪ B) = σ.Pr A + σ.Pr B
:=
begin
  rw Pr, rw finsum_mem_union' h (σ.support_of_set_finite _) (σ.support_of_set_finite _),
  refl
end

lemma Pr_empty_eq_zero (σ : fspm Ω) : σ.Pr ∅ = 0 :=
begin
  have h := σ.Pr_additive (empty_disjoint _),
  rwa [set.union_empty, self_eq_add_left] at h,
end

lemma Pr_finitely_additive (f : ℕ → set Ω) (n : ℕ) (h : pairwise (disjoint on f)) : σ.Pr (⋃ i ∈ Ico 0 n, f i) = ∑ᶠ i ∈ Ico 0 n, σ.Pr (f i) :=
begin
  induction n, 
  { rw [Ico_self, finsum_mem_empty, ← σ.Pr_empty_eq_zero,bUnion_empty] },
  case succ : n ih {
    rw [bUnion_range_succ, finsum_range_succ], rw [Pr_additive, ih],
    rw set.disjoint_bUnion_left, intros i hi,
    apply h, rintro rfl,
    apply nat_ico_range_nmem i hi,
  }
end

lemma Pr_whole_eq_one (σ : fspm Ω) : σ.Pr univ = 1 := σ.Pr_normal

lemma Pr_mono (σ : fspm Ω) : monotone σ.Pr :=
begin
  intros A B hAB,
  have h := σ.Pr_additive (disjoint_diff),
  rw [set.union_comm, diff_union_of_subset hAB] at h,
  rw [h, le_add_iff_nonneg_right],
  apply σ.Pr_nonneg
end

lemma Pr_le_one (σ : fspm Ω) (A : set Ω) : σ.Pr A ≤ 1 := 
begin
  rw ← σ.Pr_normal,
  apply σ.Pr_mono (subset_univ _)
end

lemma Pr_complement_eq_one_sub (σ : fspm Ω) (A : set Ω) : σ.Pr Aᶜ = 1 - σ.Pr A :=
  by {  rw [← σ.Pr_normal, ←union_compl_self A, Pr_additive, add_tsub_cancel_left],
        rw [set.disjoint_iff_inter_eq_empty, inter_compl_self]}

lemma Pr_total_pair_compl (σ : fspm Ω) (A B : set Ω) : σ.Pr A = σ.Pr (A ∩ B) + σ.Pr (A ∩ Bᶜ) := by rw [← σ.Pr_additive (disjoint_inter_inter_compl _ _), inter_union_compl]

/- 
TODO: Finite version of this pair lemma.
-/

lemma Pr_total_pair_diff (σ : fspm Ω) (A B : set Ω) : σ.Pr A = σ.Pr (A ∩ B) + σ.Pr (A \ B) := by {rw [diff_eq, Pr_total_pair_compl]}

lemma Pr_diff_eq_sub_Pr_inter (σ : fspm Ω) (A B : set Ω) : σ.Pr (A \ B) = σ.Pr A - σ.Pr (A ∩ B) := by rw [σ.Pr_total_pair_diff A, add_tsub_cancel_left]

lemma Pr_union_inter (σ : fspm Ω) (A B : set Ω)
  : σ.Pr (A ∪ B) + σ.Pr (A ∩ B) = σ.Pr A + σ.Pr B :=
begin
  rw union_eq_diff_union_diff_union_inter,
  rw [σ.Pr_additive (disjoint_diff_union_diff_inter _ _), σ.Pr_additive (disjoint_diff_diff A B), σ.Pr_total_pair_diff A B, σ.Pr_total_pair_diff B A, inter_comm B A],
  ring
end

lemma Pr_union_eq_inc_exc (σ : fspm Ω) (A B : set Ω)
  : σ.Pr (A ∪ B) = σ.Pr A + σ.Pr B - σ.Pr (A ∩ B) :=
begin
  rw eq_sub_iff_add_eq,
  apply σ.Pr_union_inter
end

lemma Pr_inter_le_left (σ : fspm Ω) (A B : set Ω)
  : σ.Pr (A ∩ B) ≤ σ.Pr A := σ.Pr_mono (inter_subset_left _ _)

lemma Pr_inter_le_right (σ : fspm Ω) (A B : set Ω)
  : σ.Pr (A ∩ B) ≤ σ.Pr B := σ.Pr_mono (inter_subset_right _ _)

lemma Pr_subadditive (σ : fspm Ω) (A B : set Ω) : σ.Pr (A ∪ B) ≤ σ.Pr A + σ.Pr B := by { rw [σ.Pr_union_eq_inc_exc, sub_le_self_iff], apply σ.Pr_nonneg }

lemma Pr_finitely_subadditive  (f : ℕ → set Ω) (n : ℕ) : σ.Pr (⋃ i ∈ Ico 0 n, f i) ≤ ∑ᶠ i ∈ Ico 0 n, σ.Pr (f i) :=
begin
  induction n, 
  { rw [Ico_self, finsum_mem_empty, ← σ.Pr_empty_eq_zero,bUnion_empty] },
  case succ : n ih {
    rw [bUnion_range_succ, finsum_range_succ],
    exact le_trans (σ.Pr_subadditive _ _) (add_le_add ih (by refl)),
  }
end


noncomputable def Pr_cond (σ : fspm Ω) (A B : set Ω) : ℝ := σ.Pr (A ∩ B) / σ.Pr B

lemma Pr_cond_mul_eq_Pr_inter (σ : fspm Ω) (A B : set Ω) 
  : σ.Pr (A ∩ B) = σ.Pr_cond A B * σ.Pr B := 
begin
  by_cases hB : (σ.Pr B = 0),
  { 
    rw [hB, mul_zero],
    apply ge_antisymm (Pr_nonneg _ _),
    rw ← hB,
    apply Pr_inter_le_right
  },
  { rw [Pr_cond, div_mul_cancel _ hB], },
end

lemma Pr_cond_total_pair (σ : fspm Ω) (A B : set Ω) 
  : σ.Pr A = σ.Pr_cond A B * σ.Pr B + σ.Pr_cond A Bᶜ * σ.Pr Bᶜ := 
  by rw [σ.Pr_total_pair_compl _ B, Pr_cond_mul_eq_Pr_inter, Pr_cond_mul_eq_Pr_inter]

/- 
TODO: Finite version of this pair lemma.
-/

lemma Pr_bayes {σ : fspm Ω} (A B : set Ω)
  : σ.Pr_cond A B = (σ.Pr_cond B A * σ.Pr A) / σ.Pr B  := 
begin
  rw [Pr_cond, set.inter_comm, Pr_cond_mul_eq_Pr_inter],
end

lemma Pr_total_bayes {σ : fspm Ω} (A B : set Ω)
  : σ.Pr_cond A B = (σ.Pr_cond B A * σ.Pr A) / (σ.Pr_cond B A * σ.Pr A + σ.Pr_cond B Aᶜ * σ.Pr Aᶜ) := by rw [Pr_bayes, Pr_cond_total_pair _ B A]


lemma Pr_cond_nonneg {σ : fspm Ω} {B : set Ω} (h : σ.Pr B ≠ 0 ) : ∀ (A : set Ω), 0 ≤ σ.Pr_cond A B :=
begin
  intros A,
  unfold Pr_cond,
  rw le_div_iff,
  { simp only [zero_mul],
    apply Pr_nonneg,
  },
  rw lt_iff_le_and_ne,
  exact ⟨Pr_nonneg σ B, h.symm⟩
end

lemma Pr_cond_normal {σ : fspm Ω} {B : set Ω} (h : σ.Pr B ≠ 0) : σ.Pr_cond univ B = 1 := by rw [Pr_cond, set.univ_inter, div_self h]

lemma Pr_cond_σ_add {σ : fspm Ω} {B : set Ω} (h : σ.Pr B ≠ 0) : ∀ (S T : set Ω), disjoint S T → σ.Pr_cond (S ∪ T) B = σ.Pr_cond S B + σ.Pr_cond T B :=
begin
  intros _ _ _,
  unfold Pr_cond,
  rw [set.inter_distrib_right, Pr_additive, add_div],
  apply disjoint_of_subset_left (set.inter_subset_left _ _),
  apply disjoint_of_subset_right (set.inter_subset_left _ _),
  assumption
end




end fspm

noncomputable def dirac_pr (ω x : Ω) : ℝ := if x = ω then 1 else 0

lemma dirac_pr_eq (ω x : Ω) : dirac_pr ω x = if x = ω then 1 else 0 := rfl

lemma dirac_ω (ω : Ω) : dirac_pr ω ω = 1 :=
  by { rw [dirac_pr_eq, if_pos], refl }

lemma dirac_nω (ω : Ω) : ∀ x, x ≠ ω → dirac_pr ω x = 0 := λ _ h, if_neg h

lemma dirac_support (ω : Ω) : function.support (dirac_pr ω) = {ω} :=
  by {  ext, rw [function.mem_support, dirac_pr, mem_singleton_iff, 
        ite_ne_right_iff], finish }

lemma dirac_finite (ω : Ω) : (function.support (dirac_pr ω)).finite :=
  by { rw dirac_support, apply finite_singleton }

lemma dirac_nonneg (ω x : Ω) : 0 ≤ dirac_pr ω x :=
  by { rw dirac_pr_eq, split_ifs; finish }

lemma dirac_normal (ω : Ω) : ∑ᶠ (x : Ω), dirac_pr ω x = 1 :=
  by { rw finsum_eq_single _ _ (dirac_nω _), apply dirac_ω }

noncomputable def dirac (ω : Ω) : fspm Ω := 
⟨dirac_pr ω,
dirac_finite _,
dirac_nonneg _,
dirac_normal _⟩





