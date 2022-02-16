import data.real.basic
import data.finset.basic
import algebra.big_operators.basic
import data.real.nnreal
open_locale big_operators

open finset
variables {α : Type*} [fintype α] [decidable_eq α]

structure fps (α : Type*) [fintype α] [decidable_eq α] :=
(pr : α → ℝ)
(pr_nonneg : ∀ x, 0 ≤ pr x)
(pr_normal : ∑ x, pr x = 1)

structure fpd (α : Type*) [fintype α] [decidable_eq α] :=
(Pr : finset α → ℝ)
(Pr_nonneg : ∀ A, 0 ≤ Pr A)
(Pr_normal : Pr univ = 1)
(Pr_σ_add : ∀ A B, disjoint A B → Pr (A ∪ B) = Pr A + Pr B)

namespace fps

def fpd (Ω : fps α) : fpd α :=
⟨λ A, ∑ x in A, Ω.pr x,
λ _, sum_nonneg (λ _ _, Ω.pr_nonneg _),
Ω.pr_normal,
λ _ _ h, by rw sum_union h⟩

end fps

namespace fpd

lemma Pr_empty_eq_zero (Ω : fpd α) : Ω.Pr ∅ = 0 :=
begin
  have h := Ω.Pr_σ_add ∅ ∅ (disjoint_empty_left _),
  rwa [union_empty, self_eq_add_left] at h,
end

lemma Pr_mono (Ω : fpd α) : monotone Ω.Pr
  :=
begin
  intros A B hAB,
  have h := Ω.Pr_σ_add A (B \ A),
  rw union_sdiff_of_subset hAB at h,
  rw [h disjoint_sdiff, le_add_iff_nonneg_right],
  apply Ω.Pr_nonneg
end

lemma Pr_le_one (Ω : fpd α) (A : finset α) : Ω.Pr A ≤ 1 := 
begin
  rw ← Ω.Pr_normal,
  apply Ω.Pr_mono (subset_univ _)
end


lemma Pr_sum (Ω : fpd α) (A : finset α): ∑ x in A, Ω.Pr {x} = Ω.Pr A
  :=
begin
  refine A.induction_on (by rw [Pr_empty_eq_zero, sum_empty]) _,
  intros _ _ hxA' iH,
  rw [sum_insert hxA', iH, insert_eq, Pr_σ_add _ _ _ (disjoint_singleton_left.mpr hxA')]
end

def fps (Ω : fpd α) : fps α :=
⟨λ x, Ω.Pr {x},
λ x, Ω.Pr_nonneg {x},
by {rw Pr_sum, apply Pr_normal}⟩

lemma Pr_inter_le_left (Ω : fpd α) (A B : finset α)
  : Ω.Pr (A ∩ B) ≤ Ω.Pr A := Ω.Pr_mono (inter_subset_left _ _)

lemma Pr_inter_le_right (Ω : fpd α) (A B : finset α)
  : Ω.Pr (A ∩ B) ≤ Ω.Pr B := Ω.Pr_mono (inter_subset_right _ _)

lemma Pr_union_inter (Ω : fpd α) (A B : finset α)
  : Ω.Pr (A ∪ B) + Ω.Pr (A ∩ B) = Ω.Pr A + Ω.Pr B :=
begin
  have h := Ω.Pr_σ_add A (B \ A) disjoint_sdiff,
  sorry,
end

-- Could do the next three for inter, which corresponds to submultiplicative.

lemma Pr_union_eq_inc_exc (Ω : fpd α) (A B : finset α)
  : Ω.Pr (A ∪ B) = Ω.Pr A + Ω.Pr B - Ω.Pr (A ∩ B) :=
begin
  rw eq_sub_iff_add_eq,
  apply Ω.Pr_union_inter
end

lemma Pr_subadditive (Ω : fpd α) (A B : finset α) : Ω.Pr (A ∪ B) ≤ Ω.Pr A + Ω.Pr B := 
begin
  rw Ω.Pr_union_eq_inc_exc,
  rw sub_le_self_iff,
  apply Ω.Pr_nonneg,
end

lemma Pr_finitely_subadditive {ι : Type*} [decidable_eq ι] (s : finset ι) (f : ι → finset α) (Ω : fpd α) : Ω.Pr (s.bUnion f) ≤ ∑ ι in s, Ω.Pr (f ι) := 
begin
  revert s,
  refine finset.induction (by rw [bUnion_empty, sum_empty, Ω.Pr_empty_eq_zero]) _,
  intros _ _ his iH,
  rw [bUnion_insert, sum_insert his],
  apply le_trans (Pr_subadditive _ _ _),
  rw add_le_add_iff_left,
  exact iH
end


lemma Pr_almost_disjoint_union_eq_Pr_add {Ω : fpd α} {A B : finset α} (hAB : Ω.Pr (A ∩ B) = 0) : Ω.Pr (A ∪ B) = Ω.Pr A + Ω.Pr B := by rw [Pr_union_eq_inc_exc, hAB, sub_zero]

lemma Pr_almost_disjoint_of_disjoint (Ω : fpd α) {A B : finset α} (hAB : disjoint A B) : Ω.Pr (A ∩ B) = 0 :=
begin
  rw [disjoint_iff_inter_eq_empty] at hAB,
  rw [hAB, Pr_empty_eq_zero]
end

lemma Pr_disjoint_union_eq_Pr_add {Ω : fpd α} {A B : finset α} (hAB : disjoint A B) : Ω.Pr (A ∪ B) = Ω.Pr A + Ω.Pr B := Pr_almost_disjoint_union_eq_Pr_add (Pr_almost_disjoint_of_disjoint _ hAB)

lemma Pr_sdiff_eq_Pr_sub_Pr_int (Ω : fpd α) (A B : finset α) : Ω.Pr (A \ B) = (Ω.Pr A) - Ω.Pr (A ∩ B) :=
begin
  nth_rewrite 1 ← sdiff_union_inter A B,
  rw [Pr_disjoint_union_eq_Pr_add (disjoint_sdiff_inter _ _),add_tsub_cancel_right],
end

lemma Pr_complement (Ω : fpd α) (A : finset α) : Ω.Pr Aᶜ = 1 - Ω.Pr A :=
  by rw [compl_eq_univ_sdiff, Pr_sdiff_eq_Pr_sub_Pr_int, univ_inter, Pr_normal]

lemma Pr_total_pair (Ω : fpd α) (A B : finset α) : Ω.Pr A = Ω.Pr (A ∩ B) + Ω.Pr (A ∩ Bᶜ) :=
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

lemma Pr_total_finite {ι : Type*} [decidable_eq ι] (s : finset ι) (B : ι → finset α) (h_cover : s.bUnion B = univ) (h_disjoint : pairwise (disjoint on B)) (Ω : fpd α) (A : finset α) :
  Ω.Pr A = ∑ i in s, Ω.Pr (A ∩ (B i)) := sorry

noncomputable def Pr_cond (Ω : fpd α) (A B : finset α) : ℝ := Ω.Pr (A ∩ B) / Ω.Pr B

lemma Pr_cond_mul_eq_Pr_inter (Ω : fpd α) (A B : finset α) 
  : Ω.Pr (A ∩ B) = Ω.Pr_cond A B * Ω.Pr B := 
begin
  by_cases hB : (Ω.Pr B = 0),
  { 
    rw [hB, mul_zero],
    apply ge_antisymm (Pr_nonneg _ _),
    rw ← hB,
    apply Pr_inter_le_right
  },
  { rw [Pr_cond, div_mul_cancel _ hB], },
end

lemma Pr_cond_total_pair (Ω : fpd α) (A B : finset α) 
  : Ω.Pr A = Ω.Pr_cond A B * Ω.Pr B + Ω.Pr_cond A Bᶜ * Ω.Pr Bᶜ := 
  by rw [Pr_total_pair _ _ B, Pr_cond_mul_eq_Pr_inter, Pr_cond_mul_eq_Pr_inter]

lemma Pr_cond_total_finite {ι : Type*} [decidable_eq ι] (s : finset ι) (B : ι → finset α) (h_cover : s.bUnion B = univ) (h_disjoint : pairwise (disjoint on B)) (Ω : fpd α) (A : finset α) :
  Ω.Pr A = ∑ i in s, (Ω.Pr_cond A (B i))*Ω.Pr (B i) := 
begin
  rw Pr_total_finite s B h_cover h_disjoint,
  rw sum_congr rfl,
  intros _ _,
  rw Pr_cond_mul_eq_Pr_inter
end

lemma Pr_bayes {Ω : fpd α} (A B : finset α)
  : Ω.Pr_cond A B = (Ω.Pr_cond B A * Ω.Pr A) / Ω.Pr B  := 
begin
  rw [Pr_cond, inter_comm, Pr_cond_mul_eq_Pr_inter],
end

lemma Pr_total_bayes {Ω : fpd α} (A B : finset α)
  : Ω.Pr_cond A B = (Ω.Pr_cond B A * Ω.Pr A) / (Ω.Pr_cond B A * Ω.Pr A + Ω.Pr_cond B Aᶜ * Ω.Pr Aᶜ) := by rw [Pr_bayes, Pr_cond_total_pair _ B A]

lemma Pr_cond_nonneg {Ω : fpd α} {B : finset α} (h : Ω.Pr B ≠ 0 ) : ∀ (A : finset α), 0 ≤ Ω.Pr_cond A B :=
begin
  intros A,
  unfold Pr_cond,
  rw le_div_iff,
  { simp,
    apply Pr_nonneg,
  },
  rw lt_iff_le_and_ne,
  exact ⟨Pr_nonneg Ω B, h.symm⟩
end

lemma Pr_cond_normal {Ω : fpd α} {B : finset α} (h : Ω.Pr B ≠ 0) : Ω.Pr_cond univ B = 1 := by rw [Pr_cond, univ_inter, div_self h]

lemma Pr_cond_σ_add {Ω : fpd α} {B : finset α} (h : Ω.Pr B ≠ 0) : ∀ (S T : finset α), disjoint S T → Ω.Pr_cond (S ∪ T) B = Ω.Pr_cond S B + Ω.Pr_cond T B :=
begin
  intros _ _ _,
  unfold Pr_cond,
  rw [inter_distrib_right, Pr_σ_add, add_div],
  apply disjoint_of_subset_left (inter_subset_left _ _),
  apply disjoint_of_subset_right (inter_subset_left _ _),
  assumption
end

noncomputable def Pr_cond_dist {Ω : fpd α} {B : finset α} (h : Ω.Pr B ≠ 0) : fpd α :=
⟨λ A, Ω.Pr_cond A B,
λ A, Pr_cond_nonneg h A,
Pr_cond_normal h,
λ S T, Pr_cond_σ_add h S T⟩

end fpd

/-
def rvar (Ω : fpd α) (β : Type*) := α → β 

namespace rvar

rvar.pure {Ω : fpd α} (b : β)

end rvar
-/