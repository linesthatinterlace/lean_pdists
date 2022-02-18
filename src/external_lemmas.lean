import tactic
import data.real.basic
import data.set.prod
import algebra.big_operators.finprod


namespace set

lemma inter_idem {α : Type*} (A : set α)
  : A ∩ A = A := inf_idem

lemma inter_eq_inter_inter {α : Type*} (A B : set α)
  : A ∩ B ∩ B = A ∩ B := by rw [inter_assoc, inter_idem]

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

theorem disjoint_bUnion_left {α : Type*} {t : set α} {ι : Sort*} {I : set ι} {s : ι → set α} :
disjoint (⋃ i ∈ I, s i) t ↔ ∀ i ∈ I, disjoint (s i) t :=
begin
  rw disjoint_Union_left, split; intros H i; specialize H i,
  { rwa disjoint_Union_left at H },
  { rwa disjoint_Union_left }
end

lemma nat_ico_range_succ_eq_union (n : ℕ) : Ico 0 (n + 1) = insert n (Ico 0 n) :=
begin
  ext, rw [mem_insert_iff, mem_Ico, mem_Ico, nat.lt_succ_iff_lt_or_eq], finish
end

lemma nat_ico_range_nmem (n : ℕ) : n ∉ Ico 0 n := by apply right_mem_Ico.mp

lemma nat_ico_range_finite (n : ℕ) : (Ico 0 n).finite :=
begin
  induction n with n ih,
  { rw Ico_self, apply finite_empty },
  { rw nat_ico_range_succ_eq_union,
    apply set.finite.insert _ ih
  }
end

lemma bUnion_range_succ {X : Type*} (A : ℕ → set X) (n : ℕ) :
  (⋃ i ∈ Ico 0 (n + 1), A i) = (⋃ (i ∈ Ico 0 n), A i) ∪ A n :=
begin
  rw [nat_ico_range_succ_eq_union, bUnion_insert, union_comm]
end

end set

open_locale big_operators

open set

theorem finsum_mem_nonneg {α : Sort*} {M : Type*} {s : set α} [ordered_add_comm_monoid M] {f : α → M} (hf : ∀ i ∈ s, 0 ≤ f i) :
0 ≤ ∑ᶠ i ∈ s, f i := finsum_mem_induction _ (le_refl _) (λ _ _ _ _, add_nonneg (by assumption) (by assumption)) hf

theorem finsum_range_succ {β : Type*} [add_comm_monoid β] (f : ℕ → β) (n : ℕ) : ∑ᶠ i ∈ Ico 0 (n + 1), f i = ∑ᶠ i ∈ set.Ico 0 n, f i + f n := by rw [nat_ico_range_succ_eq_union, finsum_mem_insert _ (nat_ico_range_nmem _) (nat_ico_range_finite _), add_comm]

lemma function.support_mul₂ {α : Type*} {β : Type*} {R : Type*} [semiring R] [no_zero_divisors R] (f : α → R) (g : β → R) 
: function.support (λ (xy : α × β), f xy.fst * g xy.snd) = ((function.support f) ×ˢ (function.support g)) :=
begin
  ext,
  simp only [set.mem_inter_eq, function.support_mul, set.mem_prod, function.mem_support]
end

lemma function.support_mul_finite_of_supports_finite {α : Type*} {β : Type*} {R : Type*} [semiring R] [no_zero_divisors R] {f : α → R} {g : β → R} (hf : (function.support f).finite) (hg : (function.support g).finite)
: (function.support (λ (xy : α × β), f xy.fst * g xy.snd)).finite :=
begin
  rw function.support_mul₂,
  apply set.finite.prod hf hg
end

lemma finsum_sum_mul {α : Type*} {β : Type*} {R : Type*} [semiring R] [no_zero_divisors R] {f : α → R} {g : β → R} (hf : (function.support f).finite) (hg : (function.support g).finite) : ∑ᶠ (x : α) (y : β), f x * g y = (∑ᶠ x : α, f x) * (∑ᶠ y : β, g y) :=
begin
  rw finsum_mul _ _ hf,
  rw finsum_congr, intro _,
  rw mul_finsum _ _ hg
end

lemma finsum_sum_mul_curry {α : Type*} {β : Type*} {R : Type*} [semiring R] [no_zero_divisors R] {f : α → R} {g : β → R} (hf : (function.support f).finite) (hg : (function.support g).finite) : ∑ᶠ xy : (α × β), f xy.fst * g xy.snd = (∑ᶠ x : α, f x) * (∑ᶠ y : β, g y) :=
begin
  rw finsum_curry _ (function.support_mul_finite_of_supports_finite hf hg),
  rw finsum_sum_mul hf hg
end

lemma finsum_sum_mul_curry_ish_ish {α : Type*} {β : Type*} {M : Type*} [add_comm_monoid M] {f : α → β → M} (hf : (function.support f).finite) : ∑ᶠ xy, f xy = ∑ᶠ yx, (λ yx : β × α, f (yx.snd, yx.fst)) yx :=
begin
  rw finsum_eq_of_bijective, rotate, rotate,library_search,
end

lemma finsum_sum_mul_curry_ish {α : Type*} {β : Type*} {M : Type*} [add_comm_monoid M] {f : α → β → M} (hf : (function.support f).finite) : ∑ᶠ (x : α) (y : β), f x y = ∑ᶠ (y : β) (x : α) , f x y :=
begin
  rw finsum_sum_mul_curry_ish_ish hf,
  rw ← finsum_curry (function.curry f),
end