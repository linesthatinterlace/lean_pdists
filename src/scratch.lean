-- This is content that isn't yet ready for the main file.

/-
noncomputable def cond_dist_pr {B : set Ω} (h : σ.Pr B ≠ 0) (x : Ω) : ℝ
  := σ.Pr_cond {x} B

lemma cond_dist_finite {B : set Ω} (h : σ.Pr B ≠ 0) : (function.support (σ.cond_dist_pr h)).finite := sorry

lemma cond_dist_nonneg {B : set Ω} (h : σ.Pr B ≠ 0) : ∀ (x : Ω), 0 ≤ σ.cond_dist_pr h x := sorry

lemma cond_dist_normal {B : set Ω} (h : σ.Pr B ≠ 0) : ∑ᶠ (x : Ω), σ.cond_dist_pr h x = 1 := sorry

noncomputable def cond_dist {B : set Ω} (h : σ.Pr B ≠ 0) : fspm Ω :=
⟨σ.cond_dist_pr h,
σ.cond_dist_finite _, σ.cond_dist_nonneg _, σ.cond_dist_normal _⟩

lemma cond_dist_eq_Pr_cond {A B : set Ω} (h : σ.Pr B ≠ 0)
  : (σ.cond_dist h).Pr (A ∩ B) = σ.Pr_cond A B :=
begin
  unfold Pr cond_dist, simp, unfold cond_dist_pr, unfold Pr_cond, unfold Pr, simp,
end
-/
/-

structure rvar (α : Type*) := 
(map : Ω → α)
(σ : fspm Ω)


variables {α : Type*}

namespace rvar

def Pr {σ : fspm Ω} (X : rvar α) (T : set α) : ℝ := σ.Pr (X.map⁻¹' T)

def pure {α : Type*} (b : α) : rvar α := 
⟨λ _, b,
⟨_, _, _⟩⟩
--def bind {α β : Type*} {σ : fspm Ω} (X : rvar σ α) (f : α → )
end rvar
-/