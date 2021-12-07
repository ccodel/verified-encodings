/-
This file contains the development of the Tseitin encoding for XOR

Authors: Cayden Codel, Jeremy Avidgad, Marijn Heule
Carnegie Mellon University
-/

import cnf.literal_general
import cnf.clause_general
import cnf.cnf_general
import xor.xor_general
import cnf.gensym

import data.list.basic
import data.nat.basic
import init.function

universe u

variables {V : Type u} [inhabited V] [decidable_eq V]

open literal
open clause
open cnf
open xor_gate

open list
open assignment
open function

namespace tseitin_xor

lemma dropn_len {α : Type u} {n : nat} (a : α) {l : list α} :
  n > 1 → length l > n → length (l.drop n ++ [a]) < length l :=
begin
  intros hn hl,
  induction l with x xs ih,
  { simp [lt_trans hn hl] at hl, contradiction },
  { by_cases length xs = n,
    { simp [h, gt.lt hn] },
    { simp at hl,
      have red := ih (gt.lt (array.push_back_idx hl (ne.symm h))), -- strange theorem
      simp at red,
      simp [tsub_add_eq_add_tsub (nat.lt_succ_iff.mp hl)] at red,
      simp [red] } }
end

lemma three_gt_one : 3 > 1 :=
nat.one_lt_succ_succ 1

lemma exists_three {α : Type u} : ∀ {l : list α},
  length l > 3 → ∃ (a b c : α) (L : list α), a :: b :: c :: L = l
| [] := by simp
| (a :: []) := by simp 
| (a :: b :: []) := by { simp, intro h, linarith }
| (a :: b :: c :: L) := begin
  intro _,
  use [a, b, c, L, rfl]
end

lemma restriction_injective {f : nat → V} (hf : injective f) :
  injective (λ n, f (n + 1)) :=
begin
  intros n₁ n₂ h,
  exact add_right_cancel ((injective.eq_iff hf).mp h)
end

lemma restriction_image_subset (f : nat → V) :
  set.range (λ n, f (n + 1)) ⊆ set.range f :=
begin
  intros v hv,
  rcases set.mem_range.mp hv with ⟨y, hy⟩,
  apply set.mem_range.mpr,
  use [y + 1, hy]
end

lemma restriction_first {f : nat → V} (hinj : injective f) :
  f 0 ∉ set.range (λ n, f (n + 1)) :=
begin
  intro h,
  rcases set.mem_range.mp h with ⟨y, hy⟩,
  have := (injective.eq_iff hinj).mp hy,
  contradiction
end

lemma restriction_disjoint {f : nat → V} {l : list (literal V)}
  (h : (∀ v ∈ set.range f, v ∉ (clause.vars l))) :
  ∀ v ∈ set.range (λ n, f (n + 1)), v ∉ (clause.vars l) :=
begin
  intros v hv,
  exact h v ((restriction_image_subset f) hv),
end

lemma res_disjoint {f : nat → V} {l : list (literal V)}
  (hinj : injective f)
  (h : (∀ v ∈ set.range f, v ∉ (clause.vars l))) :
  ∀ v ∈ set.range (λ n, f (n + 1)), v ∉ (clause.vars (l.drop 3 ++ [Pos (f 0)])) :=
begin
  intros v hv,
  have := (restriction_disjoint h) v hv,
  have hleft : v ∉ clause.vars (drop 3 l), exact mt 
    (λ h, vars_subset_of_subset (drop_subset 3 l) h)
    ((restriction_disjoint h) v hv),
  have hright : v ∉ clause.vars [Pos (f 0)],
  { intro hcon,
    simp [var] at hcon,
    simp at hv, -- what is being simplified here?
    rcases hv with ⟨y, rfl⟩,
    have := (injective.eq_iff hinj).mp hcon,
    contradiction },
  exact not_mem_vars_append_of_not_mem_of_not_mem hleft hright
end

-- Implementation using variable stock
def txor3 : Π (l : list (literal V)), Π (f : nat → V),
  (injective f) → (∀ v ∈ set.range f, v ∉ (clause.vars l)) → cnf V
| [] _ _ _ := [[]]
| l f hinj him := if h : length l ≤ 3 then xor_cnf l else
                  have length (l.drop 3 ++ [Pos (f 0)]) < length l,
                    from (dropn_len _ three_gt_one (not_le.mp h)),
                  (xor_cnf (l.take 3 ++ [Neg (f 0)])) ++
                  (txor3 (l.drop 3 ++ [Pos (f 0)]) (λ n, f (n + 1)) 
                    (restriction_injective hinj) (res_disjoint hinj him))
using_well_founded {
  rel_tac := λ a b, `[exact ⟨_, measure_wf (λ σ, list.length σ.1)⟩],
  dec_tac := tactic.assumption
}

theorem txor3_eq_xor_cnf_of_len_le_three {l : list (literal V)}
  {f : nat → V} (hinj : injective f) (him : ∀ v ∈ set.range f, v ∉ (clause.vars l)) :
  length l ≤ 3 → (txor3 l f hinj him) = xor_cnf l :=
begin
  intro h,
  cases l with l ls,
  { simp [txor3] },
  { unfold txor3, simp [h] }
end

-- Switch to set version of vars across the table
-- doesn't actually work, but can say that any new variables introduced don't conflict with earlier ones
/-
theorem txor3_vars_disjoint (a b c : literal V) (l : list (literal V))
  {f : nat → V} (hinj : injective f)
  (him : ∀ v ∈ set.range f, v ∉ (clause.vars l))
  (him₂ : ∀ v ∈ set.range f, v ∉ (clause.vars [a, b, c])) 
  (hdis : disjoint (clause.vars [a, b, c]) (clause.vars l)) :
  disjoint (clause.vars [a, b, c]) (cnf.vars (txor3 l f hinj him)) :=
begin
end
-/

theorem stronger (l : list (literal V)) (α : assignment V)
  {f : nat → V} (hinj : injective f)
  (him : ∀ v ∈ set.range f, v ∉ (clause.vars l)) :
  cnf.eval α (xor_cnf l) = tt →
  ∃ (α₂ : assignment V), cnf.eval α₂ (txor3 l f hinj him) = tt ∧ 
  (α ≡[clause.vars l]≡ α₂) :=
begin
  induction l using strong_induction_on_lists with l ih generalizing α f,
  by_cases hlen : length l ≤ 3,
  { rw txor3_eq_xor_cnf_of_len_le_three hinj him hlen, 
    intro h,
    use α,
    exact and.intro h (eqod.refl α _) },
  { intro h,
    rcases exists_three (not_le.mp hlen) with ⟨a, b, c, L, rfl⟩,

    unfold txor3,
    simp [hlen, cnf.eval_append],

    have c_to_app : a :: b :: c :: L = [a, b, c] ++ L, simp,
    have ha_in : a ∈ [a, b, c], simp,
    have hb_in : b ∈ [a, b, c], simp,
    have hc_in : c ∈ [a, b, c], simp,
    have hav_in : a.var ∈ clause.vars [a, b, c],
      from mem_vars_of_mem_clause ha_in,
    have hbv_in : b.var ∈ clause.vars [a, b, c],
      from mem_vars_of_mem_clause hb_in,
    have hcv_in : c.var ∈ clause.vars [a, b, c],
      from mem_vars_of_mem_clause hc_in,

    rw [c_to_app, eval_xor_cnf_eq_eval_xor_gate, xor_gate.eval_append] at h,
    
    --have ihred := ih (L ++ [Pos (f 0)]) (dropn_len _ three_gt_one (not_le.mp hlen)) 
    --  (restriction_injective hinj) (res_disjoint hinj him),

    cases h3eval : xor_gate.eval α [a, b, c],
    { simp [h3eval] at h,
      have heval : literal.eval (set_var α (f 0) ff) (Pos (f 0)) = ff,
      { simp [literal.eval, set_var] },

      have hf0_not_mem : (f 0) ∉ clause.vars L,
      { simp at him,
        rw c_to_app at him,
        intro h,
        exact (him 0) ((vars_append_subset_right _ _) h) },

      have hf0_not_mem2 : (f 0) ∉ clause.vars [a, b, c],
      { simp at him,
        rw c_to_app at him,
        intro h,
        exact (him 0) ((vars_append_subset_left _ _) h) },

      have hf0_mem : (f 0) ∈ clause.vars (L ++ [Pos (f 0)]),
      { have : f 0 ∈ clause.vars [Pos (f 0)],
          by simp [clause.vars, literal.var],
        exact (vars_append_subset_right L _) this },

      have : cnf.eval (set_var α (f 0) ff) (xor_cnf (L ++ [Pos (f 0)])) = tt,
      { rw eval_xor_cnf_eq_eval_xor_gate,
        rw xor_gate.eval_append,
        simp [literal.eval, heval],
        have : α ≡[clause.vars L]≡ (set_var α (f 0) ff),
          from eqod_set_var_of_not_mem α (f 0) ff (clause.vars L) hf0_not_mem,
        rw ← equiv_on_domain_for_xor this,
        exact h },
      
      have ihred := ih (L ++ [Pos (f 0)]) (dropn_len _ three_gt_one (not_le.mp hlen))
        (set_var α (f 0) ff)
        (restriction_injective hinj) (res_disjoint hinj him) this,
      
      rcases ihred with ⟨α₂, ha₂, heqod⟩,
      use (assignment.ite α α₂ (clause.vars [a, b, c])),
      split,
      {
        split,
        { have : [a, b, c, Neg (f 0)] = [a, b, c] ++ [Neg (f 0)], simp,
          rw [this, eval_xor_cnf_eq_eval_xor_gate, xor_gate.eval_append],
          rw xor_gate.eval_singleton,
          simp [xor_gate.eval_cons, literal.eval],
          rw ite_pos_of_lit _ _ hav_in, -- This is overly manual...
          rw ite_pos_of_lit _ _ hbv_in,
          rw ite_pos_of_lit _ _ hcv_in,
          rw ite_neg _ _ hf0_not_mem2,
          rw ← heqod (f 0) hf0_mem,
          simp [set_var],
          rw ← bxor_tt_right (literal.eval α c),
          simp only [← bool.bxor_assoc],
          rw bxor_tt_right,
          simp [xor_gate.eval_cons] at h3eval,
          simp [h3eval] },
        {
          -- Theorems on variables, subsets, etc.
          sorry,
        } },
      { intros v hv,
        unfold assignment.ite,
        rw c_to_app at hv,
        rcases exists_mem_clause_of_mem_vars hv with ⟨lit, hlit, rfl⟩,
        rcases mem_append.mp hlit with hl | hl,
        { simp [mem_vars_of_mem_clause hl] },
        { have hsetvar := heqod lit.var (mem_vars_of_mem_clause (mem_append_left [Pos (f 0)] hl)),
          unfold set_var at hsetvar,
          have := mem_vars_of_mem_clause hl,
          have := ne_of_mem_of_not_mem this hf0_not_mem,
          simp [this] at hsetvar,
          simp [hsetvar] } } },
    { -- symmetric to other case
      sorry,
    } }
end

theorem backward (l : list (literal V)) {f : nat → V} (hinj : injective f)
  (him : ∀ v ∈ set.range f, v ∉ (clause.vars l)) :
  (∃ (α : assignment V), cnf.eval α (xor_cnf l) = tt) → 
  ∃ (α₂ : assignment V), cnf.eval α₂ (txor3 l f hinj him) = tt :=
begin
  rintros ⟨α, ha⟩,
  rcases stronger l α hinj him ha with ⟨α₂, ha₂, _⟩,
  use [α₂, ha₂]
end

theorem stronger_forward (l : list (literal V)) (α : assignment V)
  {f : nat → V} (hinj : injective f)
  (him : ∀ v ∈ set.range f, v ∉ (clause.vars l)) :
  cnf.eval α (txor3 l f hinj him) = tt →
  ∃ (α₂ : assignment V), cnf.eval α₂ (xor_cnf l) = tt ∧
  (α ≡[clause.vars l]≡ α₂) :=
begin
  induction l using strong_induction_on_lists with l ih generalizing f,
  by_cases hlen : length l ≤ 3,
  { rw txor3_eq_xor_cnf_of_len_le_three hinj him hlen,
    intro h, use [α, h] },
  { rcases exists_three (not_le.mp hlen) with ⟨a, b, c, L, rfl⟩,
    unfold txor3,
    simp [hlen, cnf.eval_append],
    intros h₁ h₂,

    have ihred := ih (L ++ [Pos (f 0)]) (dropn_len _ three_gt_one (not_le.mp hlen))
      (restriction_injective hinj) (res_disjoint hinj him) h₂,
    
    rcases ihred with ⟨α₂, ha₂, heqod⟩,
    use α,
    split,
    { have c_to_app : a :: b :: c :: L = [a, b, c] ++ L, simp,
      rw c_to_app,
      have : f 0 ∈ clause.vars ([Pos (f 0)]),
        by simp [literal.var],
      have hf0_mem := (vars_append_subset_right L [Pos (f 0)]) this,
      have hf0_eval := heqod (f 0) hf0_mem,

      have heqod₂ := eqod_subset_of_eqod (vars_append_subset_left L ([Pos (f 0)])) heqod,

      rw eval_xor_cnf_eq_eval_xor_gate,
      rw eval_xor_cnf_eq_eval_xor_gate at h₁,
      rw eval_xor_cnf_eq_eval_xor_gate at ha₂,
      rw xor_gate.eval_append,
      rw xor_gate.eval_append at ha₂,
      cases heval : α₂ (f 0),
      { simp [literal.eval, heval] at ha₂,
        simp only [xor_gate.eval_cons, literal.eval, heval, hf0_eval] at h₁,
        rw xor_gate.eval_nil at h₁,
        rw bool.bxor_ff_right at h₁,
        simp only [← bool.bxor_assoc] at h₁, -- clean up manual
        rw bool.bnot_false at h₁,
        rw bxor_tt_right at h₁,
        simp at h₁,
        rw equiv_on_domain_for_xor heqod₂,
        simp [ha₂, xor_gate.eval_cons, h₁] },
      {
        simp [literal.eval, heval] at ha₂,
        simp only [xor_gate.eval_cons, literal.eval, heval, hf0_eval] at h₁,
        rw xor_gate.eval_nil at h₁,
        rw bool.bxor_ff_right at h₁,
        simp only [← bool.bxor_assoc] at h₁, -- clean up manual
        rw bool.bnot_true at h₁,
        rw bool.bxor_ff_right at h₁,
        simp at h₁,
        rw equiv_on_domain_for_xor heqod₂,
        simp [ha₂, xor_gate.eval_cons, h₁] } },
    { exact eqod.refl α _ } }
end

theorem forward (l : list (literal V)) {f : nat → V} (hinj : injective f)
  (him : ∀ v ∈ set.range f, v ∉ (clause.vars l)) :
 (∃ (α : assignment V), cnf.eval α (txor3 l f hinj him) = tt) → 
  ∃ (α₂ : assignment V), cnf.eval α₂ (xor_cnf l) = tt :=
begin
  rintros ⟨α, ha⟩,
  rcases stronger_forward l α hinj him ha with ⟨α₂, ha₂, _⟩,
  use [α₂, ha₂]
end


/-
theorem forward (l : list (literal V)) {f : nat → V} (hinj : injective f)
  (him : ∀ v ∈ set.range f, v ∉ (clause.vars l)) :
  (∃ (α : assignment V), cnf.eval α (txor3 l f hinj him) = tt) →
  ∃ (α₂ : assignment V), cnf.eval α₂ (xor_cnf l) = tt :=
begin
    have hperm : [Neg (f 0), a, b, c] ~ [a, b, c, Neg (f 0)],
      { have p1 := perm.cons b (perm.swap c (Neg (f 0)) []),
        have p2 := perm.swap b (Neg (f 0)) [c],
        have p3 := perm.trans p2 p1,
        have p4 := perm.cons a p3,
        have p5 := perm.swap a (Neg (f 0)) [b, c],
        exact perm.trans p5 p4 },

    cases heval0 : α₂ (f 0),
    {
      rw eval_xor_cnf_eq_eval_xor_gate (L ++ [Pos (f 0)]) α₂ at ha₂,
      rw (eval_eq_of_perm α₂ (perm_append_singleton (Pos (f 0)) L)) at ha₂,
      rw xor_gate.eval_cons at ha₂,
      simp [heval0, literal.eval] at ha₂,
    }
  }
  { simp [txor3] },
  {
    by_cases h : length (l :: ls) ≤ 3,
    { unfold txor3,
      simp [h],
      intros α ha,
      use [α, ha] },
    {
      rcases exists_three (not_le.mp h) with ⟨a, b, c, L, hls⟩,
      rcases head_eq_of_cons_eq hls with rfl,
      rcases tail_eq_of_cons_eq hls with rfl,
      simp [add_assoc] at h,
      rintros ⟨α, ha⟩,
      unfold txor3 at ha,
      simp [add_assoc, h, eval_append] at ha,
      rcases ha with ⟨h₁, h₂⟩,

      -- Reduction of induction hypothesis
      have hinjr := restriction_injective hinj,
      have himr := res_disjoint hinj him,

      rw eval_xor_cnf_eq_eval_xor_gate at h₁,
      rw h₁ at this,
      rw xor_gate.eval_cons at this,
      cases hf : α (f 0),
      {
        simp [literal.eval, hf] at this,

      }
    }
  }

-/

end tseitin_xor