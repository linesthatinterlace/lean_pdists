import data.real.basic
import data.set.finite
import algebra.big_operators.finprod
import data.real.nnreal
import algebra.support

namespace set

lemma disjoint_inter_inter_compl {α : Type*} (A B : set α)
  : disjoint (A ∩ B) (A ∩ Bᶜ) :=
begin
  apply disjoint.inter_left',
  apply disjoint.inter_right',
  rw [disjoint_iff_inter_eq_empty, inter_compl_self]
end

lemma disjoint_diff_diff {α : Type*} (A B : set α) : disjoint (A \ B) (B \ A)
  := disjoint_of_subset_left (diff_subset A B) disjoint_diff

lemma disjoint_diff_union_diff_inter {α : Type*} (A B : set α) : disjoint (A \ B ∪ B \ A) (A ∩ B)
  := 
begin
  rw disjoint_union_left,
  split;
  [ apply disjoint_of_subset_right (inter_subset_right  A B),
    apply disjoint_of_subset_right (inter_subset_left   A B)];
  { rw disjoint.comm, apply disjoint_diff }
end


end set

open_locale classical big_operators

open set set.finite function

structure fpmf (Ω : Type*) [fintype Ω] :=
(pr : Ω → ℝ)
(pr_nonneg : ∀ x, 0 ≤ pr x)
(pr_normal : ∑ᶠ x, pr x = 1)

structure fps (Ω : Type*) [fintype Ω] :=
(Pr : set Ω → ℝ)
(Pr_nonneg : ∀ A, 0 ≤ Pr A)
(Pr_normal : Pr univ = 1)
(Pr_σ_add : ∀ {A B}, disjoint A B → Pr (A ∪ B) = Pr A + Pr B)

variables {Ω : Type*} [fintype Ω]

namespace fpmf

noncomputable def fps (fp : fpmf Ω) : fps Ω :=
⟨λ A, ∑ᶠ x ∈ A, fp.pr x,
by {  intros A, rw finsum_mem_eq_finite_to_finset_sum _ (of_fintype A),
      refine finset.sum_nonneg (λ _ _, (fp.pr_nonneg _))},
by {  rw finsum_mem_univ, apply fp.pr_normal},
by {  intros A B h, rw finsum_mem_union h (of_fintype A) (of_fintype B)} ⟩

end fpmf

namespace fps

@[simp]
lemma Pr_empty_eq_zero (σ : fps Ω) : σ.Pr ∅ = 0 :=
begin
  have h := σ.Pr_σ_add (empty_disjoint _),
  rwa [union_empty, self_eq_add_left] at h,
end

@[simp]
lemma Pr_whole_eq_one (σ : fps Ω) : σ.Pr univ = 1 := σ.Pr_normal

lemma Pr_mono (σ : fps Ω) : monotone σ.Pr :=
begin
  intros A B hAB,
  have h := σ.Pr_σ_add (disjoint_diff),
  rw [union_comm, diff_union_of_subset hAB] at h,
  rw [h, le_add_iff_nonneg_right],
  apply σ.Pr_nonneg
end

lemma Pr_le_one (σ : fps Ω) (A : set Ω) : σ.Pr A ≤ 1 := 
begin
  rw ← σ.Pr_normal,
  apply σ.Pr_mono (subset_univ _)
end

@[simp]
lemma Pr_complement_eq_one_sub (σ : fps Ω) (A : set Ω) : σ.Pr Aᶜ = 1 - σ.Pr A :=
  by {  rw [← σ.Pr_normal, ←union_compl_self A, Pr_σ_add, add_tsub_cancel_left],
        rw [disjoint_iff_inter_eq_empty, inter_compl_self]}

lemma Pr_total_pair_compl (σ : fps Ω) (A B : set Ω) : σ.Pr A = σ.Pr (A ∩ B) + σ.Pr (A ∩ Bᶜ) := by rw [← σ.Pr_σ_add (disjoint_inter_inter_compl _ _), inter_union_compl]

lemma Pr_total_pair_diff (σ : fps Ω) (A B : set Ω) : σ.Pr A = σ.Pr (A ∩ B) + σ.Pr (A \ B) := by {rw [diff_eq, Pr_total_pair_compl]}

lemma Pr_diff_eq_sub_Pr_inter (σ : fps Ω) (A B : set Ω) : σ.Pr (A \ B) = σ.Pr A - σ.Pr (A ∩ B) := by rw [σ.Pr_total_pair_diff A, add_tsub_cancel_left]

lemma Pr_union_inter (σ : fps Ω) (A B : set Ω)
  : σ.Pr (A ∪ B) + σ.Pr (A ∩ B) = σ.Pr A + σ.Pr B :=
begin
  rw union_eq_diff_union_diff_union_inter,
  rw [σ.Pr_σ_add (disjoint_diff_union_diff_inter _ _), σ.Pr_σ_add (disjoint_diff_diff A B), σ.Pr_total_pair_diff A B, σ.Pr_total_pair_diff B A, inter_comm B A],
  ring
end

lemma Pr_union_eq_inc_exc (σ : fps Ω) (A B : set Ω)
  : σ.Pr (A ∪ B) = σ.Pr A + σ.Pr B - σ.Pr (A ∩ B) :=
begin
  rw eq_sub_iff_add_eq,
  apply σ.Pr_union_inter
end

lemma Pr_sum (σ : fps Ω) (A : set Ω): ∑ᶠ x ∈ A, σ.Pr {x} = σ.Pr A
  :=
begin
  apply set.finite.induction_on (of_fintype A),
  { rw [finsum_mem_empty, σ.Pr_empty_eq_zero] },
  { intros x A' hxA' hA' iH,
    rw [finsum_mem_insert _ hxA' hA', iH, insert_eq, Pr_σ_add _ (disjoint_singleton_left.mpr hxA')]
  }
end

def fpmf (σ : fps Ω) : fpmf Ω :=
⟨λ x, σ.Pr {x},
λ x, σ.Pr_nonneg {x},
by {rw [← finsum_mem_univ, Pr_sum], apply Pr_normal}⟩

lemma Pr_inter_le_left (σ : fps Ω) (A B : set Ω)
  : σ.Pr (A ∩ B) ≤ σ.Pr A := σ.Pr_mono (inter_subset_left _ _)

lemma Pr_inter_le_right (σ : fps Ω) (A B : set Ω)
  : σ.Pr (A ∩ B) ≤ σ.Pr B := σ.Pr_mono (inter_subset_right _ _)

lemma Pr_subadditive (σ : fps Ω) (A B : set Ω) : σ.Pr (A ∪ B) ≤ σ.Pr A + σ.Pr B := by { rw [σ.Pr_union_eq_inc_exc, sub_le_self_iff], apply σ.Pr_nonneg }

lemma Pr_finitely_subadditive {ι : Type*} [decidable_eq ι] (s : finset ι) (f : ι → set Ω) (σ : fps Ω) : σ.Pr (⋃ i ∈ s, f i) ≤ ∑ᶠ i ∈ s, σ.Pr (f i) := 
begin
  sorry,
end

lemma Pr_countably_subadditive (f : ℕ → set Ω) (σ : fps Ω) : σ.Pr (⋃ i, f i) ≤ ∑ᶠ i, σ.Pr (f i) := 
begin
  sorry,
end

lemma Pr_almost_disjoint_union_eq_Pr_add {σ : fps Ω} {A B : set Ω} (hAB : σ.Pr (A ∩ B) = 0) : σ.Pr (A ∪ B) = σ.Pr A + σ.Pr B := by rw [Pr_union_eq_inc_exc, hAB, sub_zero]

lemma Pr_almost_disjoint_of_disjoint (σ : fps Ω) {A B : set Ω} (hAB : disjoint A B) : σ.Pr (A ∩ B) = 0 :=
begin
  rw [disjoint_iff_inter_eq_empty] at hAB,
  rw [hAB, Pr_empty_eq_zero]
end

lemma Pr_disjoint_union_eq_Pr_add {σ : fps Ω} {A B : set Ω} (hAB : disjoint A B) : σ.Pr (A ∪ B) = σ.Pr A + σ.Pr B := Pr_almost_disjoint_union_eq_Pr_add (Pr_almost_disjoint_of_disjoint _ hAB)

lemma Pr_total_finite {ι : Type*} (s : finset ι) (B : ι → set Ω) (h_cover : (⋃ i ∈ s, B i) = univ) (h_disjoint : pairwise (disjoint on B)) (σ : fps Ω) (A : set Ω) : σ.Pr A = ∑ᶠ i ∈ s, σ.Pr (A ∩ (B i)) := sorry

noncomputable def Pr_cond (σ : fps Ω) (A B : set Ω) : ℝ := σ.Pr (A ∩ B) / σ.Pr B

lemma Pr_cond_mul_eq_Pr_inter (σ : fps Ω) (A B : set Ω) 
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

lemma Pr_cond_total_pair (σ : fps Ω) (A B : set Ω) 
  : σ.Pr A = σ.Pr_cond A B * σ.Pr B + σ.Pr_cond A Bᶜ * σ.Pr Bᶜ := 
  by rw [σ.Pr_total_pair_compl _ B, Pr_cond_mul_eq_Pr_inter, Pr_cond_mul_eq_Pr_inter]

lemma Pr_cond_total_finite {ι : Type*} (s : finset ι) (B : ι → set Ω) (h_cover : (⋃ i ∈ s, B i) = univ) (h_disjoint : pairwise (disjoint on B)) (σ : fps Ω) (A : set Ω) :
  σ.Pr A = ∑ᶠ i ∈ s, (σ.Pr_cond A (B i))*σ.Pr (B i) := sorry

lemma Pr_bayes {σ : fps Ω} (A B : set Ω)
  : σ.Pr_cond A B = (σ.Pr_cond B A * σ.Pr A) / σ.Pr B  := 
begin
  rw [Pr_cond, inter_comm, Pr_cond_mul_eq_Pr_inter],
end

lemma Pr_total_bayes {σ : fps Ω} (A B : set Ω)
  : σ.Pr_cond A B = (σ.Pr_cond B A * σ.Pr A) / (σ.Pr_cond B A * σ.Pr A + σ.Pr_cond B Aᶜ * σ.Pr Aᶜ) := by rw [Pr_bayes, Pr_cond_total_pair _ B A]

lemma Pr_cond_nonneg {σ : fps Ω} {B : set Ω} (h : σ.Pr B ≠ 0 ) : ∀ (A : set Ω), 0 ≤ σ.Pr_cond A B :=
begin
  intros A,
  unfold Pr_cond,
  rw le_div_iff,
  { simp,
    apply Pr_nonneg,
  },
  rw lt_iff_le_and_ne,
  exact ⟨Pr_nonneg σ B, h.symm⟩
end

lemma Pr_cond_normal {σ : fps Ω} {B : set Ω} (h : σ.Pr B ≠ 0) : σ.Pr_cond univ B = 1 := by rw [Pr_cond, univ_inter, div_self h]

lemma Pr_cond_σ_add {σ : fps Ω} {B : set Ω} (h : σ.Pr B ≠ 0) : ∀ (S T : set Ω), disjoint S T → σ.Pr_cond (S ∪ T) B = σ.Pr_cond S B + σ.Pr_cond T B :=
begin
  intros _ _ _,
  unfold Pr_cond,
  rw [inter_distrib_right, Pr_σ_add, add_div],
  apply disjoint_of_subset_left (inter_subset_left _ _),
  apply disjoint_of_subset_right (inter_subset_left _ _),
  assumption
end

noncomputable def Pr_cond_dist {σ : fps Ω} {B : set Ω} (h : σ.Pr B ≠ 0) : fps Ω :=
⟨λ A, σ.Pr_cond A B,
λ A, Pr_cond_nonneg h A,
Pr_cond_normal h,
λ S T, Pr_cond_σ_add h S T⟩

noncomputable def dirac (ω : Ω) : fps Ω := 
⟨λ A, ite (ω ∈ A) 1 0,
by {intros _, split_ifs; [apply zero_le_one, refl]},
by {split_ifs with h; [refl, apply false.elim (h (mem_univ _))]},
by {  intros A B hAB,
      by_cases hA: ω ∈ A;
      [{ simp [hA, hAB], apply disjoint_left.mp hAB hA }, simp [hA, hAB] ] }⟩
end fps

noncomputable def trivial : fps Ω := 
⟨λ A, ite (A = univ) 1 0,
by {intros _, split_ifs; [apply zero_le_one, refl]},
by simp,
by { intros A B hAB, }⟩
end fps

structure rvar (α : Type*) := 
(map : Ω → α)
(σ : fps Ω)


variables {α : Type*}

namespace rvar

def Pr {σ : fps Ω} (X : rvar α) (T : set α) : ℝ := σ.Pr (X.map⁻¹' T)

def pure {α : Type*} (b : α) : rvar α := 
⟨λ _, b,
⟨_, _, _⟩⟩
--def bind {α β : Type*} {σ : fps Ω} (X : rvar σ α) (f : α → )
end rvar
