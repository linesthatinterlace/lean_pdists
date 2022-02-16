import data.real.basic
import data.finset.basic
import algebra.big_operators.basic
import data.real.nnreal
open_locale big_operators
open finset

structure fps (α : Type*) [fintype α] [decidable_eq α] :=
(pr : α → ℝ)
(pr_nonneg : ∀ x, 0 ≤ pr x)
(pr_sum : ∑ x, pr x = 1)

variables {α : Type*} [fintype α] [decidable_eq α]

def fps.Pr (Ω : fps α) (A : finset α) : ℝ := ∑ x in A, Ω.pr x

@[simp]
lemma Pr_empty_eq_zero (Ω : fps α) : Ω.Pr ∅ = 0 := sum_empty

@[simp]
lemma Pr_univ_eq_one (Ω : fps α) : Ω.Pr univ = 1 := Ω.pr_sum

@[simp]
lemma Pr_singleton_eq_pr (Ω : fps α) (x : α) : Ω.pr x = Ω.Pr {x} :=
begin
  unfold fps.Pr,
  rw finset.sum_singleton
end

lemma Pr_mono (Ω : fps α) : monotone Ω.Pr
  :=
begin
  intros _ _ hAB,
  apply sum_le_sum_of_subset_of_nonneg hAB,
  intros _ _ _,
  apply Ω.pr_nonneg
end

lemma Pr_nonneg (Ω : fps α) (A : finset α) : 0 ≤ Ω.Pr A := 
begin
  rw ← Pr_empty_eq_zero Ω,
  apply Pr_mono Ω (empty_subset _)
end

lemma Pr_le_one (Ω : fps α) (A : finset α) : Ω.Pr A ≤ 1 := 
begin
  rw ← Pr_univ_eq_one Ω,
  apply Pr_mono Ω (subset_univ _)
end

lemma Pr_inter_le_left (Ω : fps α) (A B : finset α)
  : Ω.Pr (A ∩ B) ≤ Ω.Pr A := Pr_mono Ω (inter_subset_left _ _)

lemma Pr_inter_le_right (Ω : fps α) (A B : finset α)
  : Ω.Pr (A ∩ B) ≤ Ω.Pr B := Pr_mono Ω (inter_subset_right _ _)

lemma Pr_union_inter (Ω : fps α) (A B : finset α)
  : Ω.Pr (A ∪ B) + Ω.Pr (A ∩ B) = Ω.Pr A + Ω.Pr B := sum_union_inter

-- Could do the next three for inter, which corresponds to submultiplicative.

lemma Pr_union_eq_inc_exc (Ω : fps α) (A B : finset α)
  : Ω.Pr (A ∪ B) = Ω.Pr A + Ω.Pr B - Ω.Pr (A ∩ B) :=
begin
  rw eq_sub_iff_add_eq,
  apply Pr_union_inter,
end

lemma Pr_subadditive (Ω : fps α) (A B : finset α) : Ω.Pr (A ∪ B) ≤ Ω.Pr A + Ω.Pr B := 
begin
  rw Pr_union_eq_inc_exc,
  rw sub_le_self_iff,
  apply Pr_nonneg
end

lemma Pr_finitely_subadditive {ι : Type*} [decidable_eq ι] (s : finset ι) (f : ι → finset α) (Ω : fps α) : Ω.Pr (s.bUnion f) ≤ ∑ ι in s, Ω.Pr (f ι) := 
begin
  revert s,
  refine finset.induction (by rw [bUnion_empty, sum_empty, Pr_empty_eq_zero]) _,
  intros _ _ his iH,
  rw [bUnion_insert, sum_insert his],
  apply le_trans (Pr_subadditive _ _ _),
  rw add_le_add_iff_left,
  exact iH
end

lemma Pr_almost_disjoint_union_eq_Pr_add {Ω : fps α} {A B : finset α} (hAB : Ω.Pr (A ∩ B) = 0) : Ω.Pr (A ∪ B) = Ω.Pr A + Ω.Pr B := by rw [Pr_union_eq_inc_exc, hAB, sub_zero]

lemma Pr_almost_disjoint_of_disjoint (Ω : fps α) {A B : finset α} (hAB : disjoint A B) : Ω.Pr (A ∩ B) = 0 :=
begin
  rw [disjoint_iff_inter_eq_empty] at hAB,
  rw [hAB, Pr_empty_eq_zero]
end

lemma Pr_disjoint_union_eq_Pr_add {Ω : fps α} {A B : finset α} (hAB : disjoint A B) : Ω.Pr (A ∪ B) = Ω.Pr A + Ω.Pr B := Pr_almost_disjoint_union_eq_Pr_add (Pr_almost_disjoint_of_disjoint _ hAB)

lemma Pr_sdiff_eq_Pr_sub_Pr_int (Ω : fps α) (A B : finset α) : Ω.Pr (A \ B) = (Ω.Pr A) - Ω.Pr (A ∩ B) :=
begin
  nth_rewrite 1 ← sdiff_union_inter A B,
  rw [Pr_disjoint_union_eq_Pr_add (disjoint_sdiff_inter _ _),add_tsub_cancel_right],
end

lemma Pr_complement (Ω : fps α) (A : finset α) : Ω.Pr Aᶜ = 1 - Ω.Pr A :=
  by rw [compl_eq_univ_sdiff, Pr_sdiff_eq_Pr_sub_Pr_int, univ_inter, Pr_univ_eq_one]

lemma Pr_total_pair (Ω : fps α) (A B : finset α) : Ω.Pr A = Ω.Pr (A ∩ B) + Ω.Pr (A ∩ Bᶜ) :=
begin
  have inter_union_compl : A = A ∩ B ∪ A ∩ Bᶜ,
  { rw [compl_eq_univ_sdiff, inter_sdiff, inter_univ],
    nth_rewrite 0 ← sdiff_union_inter A B,
    rw union_comm
  },
  have disjoint_inter_inter_compl : disjoint (A ∩ B) (A ∩ Bᶜ),
  { rw disjoint_iff_inter_eq_empty,
    rw inter_assoc,
    nth_rewrite 1 ← inter_comm,
    rw inter_assoc,
    nth_rewrite 2 ← inter_comm,
    rw [inter_compl, inter_empty, inter_empty],
  },
  nth_rewrite 0 inter_union_compl,
  exact Pr_disjoint_union_eq_Pr_add disjoint_inter_inter_compl,
end

lemma Pr_total_finite {ι : Type*} [decidable_eq ι] (s : finset ι) (B : ι → finset α) (h_cover : s.bUnion B = univ) (h_disjoint : pairwise (disjoint on B)) (Ω : fps α) (A : finset α) :
  Ω.Pr A = ∑ i in s, Ω.Pr (A ∩ (B i)) := sorry

noncomputable def fps.Pr_cond (Ω : fps α) (A B : finset α) : ℝ := Ω.Pr (A ∩ B) / Ω.Pr B

lemma Pr_cond_mul_eq_Pr_inter (Ω : fps α) (A B : finset α) 
  : Ω.Pr (A ∩ B) = Ω.Pr_cond A B * Ω.Pr B := 
begin
  by_cases hB : (Ω.Pr B = 0),
  { 
    rw [hB, mul_zero],
    apply ge_antisymm (Pr_nonneg _ _),
    rw ← hB,
    apply Pr_inter_le_right
  },
  { rw [fps.Pr_cond, div_mul_cancel _ hB], },
end

lemma Pr_cond_total_pair (Ω : fps α) (A B : finset α) 
  : Ω.Pr A = Ω.Pr_cond A B * Ω.Pr B + Ω.Pr_cond A Bᶜ * Ω.Pr Bᶜ := 
  by rw [Pr_total_pair _ _ B, Pr_cond_mul_eq_Pr_inter, Pr_cond_mul_eq_Pr_inter]

lemma Pr_cond_total_finite {ι : Type*} [decidable_eq ι] (s : finset ι) (B : ι → finset α) (h_cover : s.bUnion B = univ) (h_disjoint : pairwise (disjoint on B)) (Ω : fps α) (A : finset α) :
  Ω.Pr A = ∑ i in s, (Ω.Pr_cond A (B i))*Ω.Pr (B i) := 
begin
  rw Pr_total_finite s B h_cover h_disjoint,
  rw sum_congr rfl,
  intros _ _,
  rw Pr_cond_mul_eq_Pr_inter
end

lemma Pr_bayes {Ω : fps α} (A B : finset α)
  : Ω.Pr_cond A B = (Ω.Pr_cond B A * Ω.Pr A) / Ω.Pr B  := 
begin
  rw [fps.Pr_cond, inter_comm, Pr_cond_mul_eq_Pr_inter],
end

lemma Pr_total_bayes {Ω : fps α} (A B : finset α)
  : Ω.Pr_cond A B = (Ω.Pr_cond B A * Ω.Pr A) / (Ω.Pr_cond B A * Ω.Pr A + Ω.Pr_cond B Aᶜ * Ω.Pr Aᶜ) := by rw [Pr_bayes, Pr_cond_total_pair _ B A]

lemma Pr_cond_nonneg {Ω : fps α} {A : finset α} (h : Ω.Pr A ≠ 0 ) : ∀ (x : α), 0 ≤ Ω.Pr_cond {x} A :=
begin
  intros x,
  unfold fps.Pr_cond,
  rw le_div_iff,
  { simp,
    apply Pr_nonneg,
  },
  { rw lt_iff_le_and_ne,
    exact ⟨Pr_nonneg Ω A, h.symm⟩
  }
end

lemma Pr_cond_normal {Ω : fps α} {A : finset α} (h : Ω.Pr A ≠ 0) : ∑ (x : α), Ω.Pr_cond {x} A = 1 :=
begin
  have compl_val : ∑ (i : α) in Aᶜ, Ω.Pr ({i} ∩ A) = 0,
  { apply sum_eq_zero,
    intros x hx,
    rw mem_compl at hx,
    rw [singleton_inter_of_not_mem hx, Pr_empty_eq_zero]
  },
  have prob_simp : ∀ i ∈ A, Ω.Pr ({i} ∩ A) = Ω.pr i,
  { intros _ hi,
    rw [singleton_inter_of_mem hi, Pr_singleton_eq_pr],
  },
  have in_val : ∑ i in A, Ω.Pr ({i} ∩ A) = Ω.Pr A,
  { rw fps.Pr,
    apply sum_congr rfl prob_simp,
  },
  unfold fps.Pr_cond,
  rw [← sum_div, ← sum_compl_add_sum A, compl_val, in_val, zero_add, div_self h]
end

noncomputable def Pr_cond_dist {Ω : fps α} {A : finset α} (h : Ω.Pr A ≠ 0) : fps α :=
⟨λ x, Ω.Pr_cond {x} A, Pr_cond_nonneg h, Pr_cond_normal h⟩

