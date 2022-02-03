/-
This file contains the development of the Tseitin encoding for XOR.
Both the pooled and linear encodigns are included here.

Authors: Cayden Codel, Jeremy Avidgad, Marijn Heule
Carnegie Mellon University
-/

import cnf.literal
import cnf.clause
import cnf.cnf
import cnf.gensym
import xor.xor
import xor.direct_xor

import data.list.basic
import data.nat.basic

universe u

variables {V : Type u} [inhabited V] [decidable_eq V]

open literal
open clause
open cnf
open nxor

open list
open assignment
open function

namespace tseitin_xor

lemma disjoint_fresh_of_disjoint {x : nxor V} {g : gensym V} {k : nat} (hk : k ≥ 3) :
  disjoint g.stock x.vars → 
  disjoint g.fresh.2.stock (nxor.vars ((Pos g.fresh.1) :: (x.drop (k - 1)))) :=
begin
  intro h,
  apply set.disjoint_right.mpr,
  intros v hv,
  simp [vars, clause.vars] at hv,
  rcases hv with rfl | hv,
  { rw var,
    exact gensym.fresh_not_mem_fresh_stock g },
  { intro hcon,
    have := clause.vars_subset_of_subset (drop_subset (k - 1) x),
    rw set.disjoint_right at h,
    exact absurd ((gensym.fresh_stock_subset g) hcon) (h (this hv)) }
end

lemma drop_len_lt {k : nat} {x : nxor V} (l : literal V) :
  k ≥ 3 → length x > k → length (l :: (x.drop (k - 1))) < length x :=
begin
  intros hk hx,
  rw length_cons,
  rcases exists_append_of_gt_length hx with ⟨x₁, x₂, rfl, hx₁⟩,
  simp only [hx₁, length_drop, length_append],
  rw [add_comm k x₂.length, nat.add_sub_assoc (nat.sub_le k 1),
      nat.sub_sub_self (nat.le_of_add_le_right hk), add_assoc],
  apply add_lt_add_left,
  exact nat.succ_le_iff.mp hk,
end

-- Note: x and g can be made implicit args, but explicit feels better
def linear_xor {k : nat} (hk : k ≥ 3) : Π (x : nxor V), Π (g : gensym V),
  (disjoint g.stock x.vars) → cnf V
| x g hdis := if h : length x ≤ k then direct_xor x else
                have length ((Pos g.fresh.1) :: (x.drop (k - 1))) < length x,
                  from (drop_len_lt _ hk (not_le.mp h)),
                (direct_xor (x.take (k - 1) ++ [(Neg g.fresh.1)])) ++
                (linear_xor ((Pos g.fresh.1) :: (x.drop (k - 1))) (g.fresh.2)
                (disjoint_fresh_of_disjoint hk hdis))
using_well_founded {
  rel_tac := λ a b, `[exact ⟨_, measure_wf (λ σ, list.length σ.1)⟩],
  dec_tac := tactic.assumption
}

/-
def linear_xor2 {k : nat} (hk : k ≥ 3) (x : nxor V) (g : gensym V)
  (hg : disjoint g.stock x.vars) : nxor V → cnf V
| x₁ := if h : length x₁ ≤ k then direct_xor x₁ else
                have length ((Pos g.fresh.1) :: (x₁.drop k)) < length x₁,
                  from (drop_len_lt _ hk (not_le.mp h)),
                (direct_xor (x₁.take k ++ [(Neg g.fresh.1)])) ++
                (linear_xor2 ((Pos g.fresh.1) :: (x₁.drop k)))
using_well_founded {
  rel_tac := λ a b, `[exact ⟨_, measure_wf (λ σ, list.length σ)⟩],
  dec_tac := tactic.assumption
}
-/

lemma linear_base_case {k : nat} (hk : k ≥ 3) {x : nxor V} {g : gensym V}
  (hdis : disjoint g.stock x.vars) : 
  length x ≤ k → linear_xor hk x g hdis = direct_xor x :=
assume h, by { rw linear_xor, simp only [h, if_true] }

lemma eqsat_forward {k : nat} (hk : k ≥ 3) {x : nxor V} {g : gensym V}
  (hdis : disjoint g.stock x.vars) {α : assignment V} :
  cnf.eval α (linear_xor hk x g hdis) = tt → cnf.eval α (direct_xor x) = tt :=
begin
  induction x using strong_induction_on_lists with x ih generalizing g,
  by_cases hx : length x ≤ k,
  { rw linear_base_case hk hdis hx, exact id },
  { intro h,
    rw linear_xor at h,
    simp [hx, cnf.eval_append] at h,
    rcases h with ⟨hdir, hrec⟩,
    rw not_le at hx,
    have h₁ := drop_len_lt (Pos g.fresh.1) hk hx,
    have h₂ := disjoint_fresh_of_disjoint hk hdis,
    have ihred := ih _ h₁ h₂ hrec,
    rw [eval_direct_xor_eq_eval_nxor, eval_eq_bodd_count_tt] at ihred,
    rw [eval_direct_xor_eq_eval_nxor, eval_eq_bodd_count_tt] at hdir,
    rw [eval_direct_xor_eq_eval_nxor, eval_eq_bodd_count_tt],
    have := take_append_drop (k - 1) x,
    have := congr_arg ((clause.count_tt α)) this,
    have := congr_arg (nat.bodd) this,
    cases hnew : (α g.fresh.1),
    { simp [count_tt_cons, hnew, literal.eval] at ihred,
      simp [count_tt_append, hnew, literal.eval] at hdir,
      rw [count_tt_append, nat.bodd_add, hdir, ihred, ff_bxor] at this,
      exact this.symm },
    { simp [count_tt_cons, hnew, literal.eval] at ihred,
      simp [count_tt_append, hnew, literal.eval] at hdir,
      rw [count_tt_append, nat.bodd_add, hdir, ihred, bxor_ff] at this,
      exact this.symm } }
end

lemma eqsat_backward {k : nat} (hk : k ≥ 3) {x : nxor V} {g : gensym V}
  (hdis : disjoint g.stock x.vars) {α : assignment V} :
  cnf.eval α (direct_xor x) = tt → (∃ (α₂ : assignment V), 
  cnf.eval α₂ (linear_xor hk x g hdis) = tt ∧ eqod α α₂ x.vars) :=
begin
  induction x using strong_induction_on_lists with x ih generalizing g α,
  by_cases hx : length x ≤ k,
  { intro h, use α, rw linear_base_case hk hdis hx,
    exact ⟨h, eqod.refl _ _⟩ },
  { intro h,

    rw [eval_direct_xor_eq_eval_nxor, eval_eq_bodd_count_tt] at h,
    have := take_append_drop (k - 1) x,
    rw [← this, count_tt_append, nat.bodd_add] at h,

    -- Proof that fresh not in x.vars
    have := set.disjoint_left.mp hdis (gensym.fresh_mem_stock g),


    have h₁ := drop_len_lt (Pos g.fresh.1) hk (not_le.mp hx),
    have h₂ := disjoint_fresh_of_disjoint hk hdis,
    have ihred := ih _ h₁ h₂,



    cases hc : nat.bodd (clause.count_tt α (take (k - 1) x)),
    {
      rw [hc, ff_bxor] at h,
      have : clause.count_tt (assignment.ite (nxor.vars x) α all_ff) ((Pos g.fresh.1) :: (drop (k - 1) x)) = clause.count_tt α (drop (k - 1) x),
      {
        rw count_tt_cons,

      }
    },
    {

    }



  }
end

theorem linear_xor_eqsat {k : nat} (hk : k ≥ 3) {x : nxor V} {g : gensym V}
  (hdis : disjoint g.stock x.vars) :
  assignment.eqsat (λ α, cnf.eval α (linear_xor hk x g hdis)) 
                   (λ α, cnf.eval α (direct_xor x)) :=
begin
  split,
  { rintros ⟨α, hl⟩,
    use α, simp at *,
    exact eqsat_forward hk hdis hl },
  { induction x using strong_induction_on_lists with x ih generalizing g,
    rintros ⟨α, hd⟩,
    simp at *,
    by_cases hx : length x ≤ k,
    { use α,
      rw linear_xor,
      simp only [hx, hd, if_true] },
    { rw linear_xor,
      simp [hx],
      rw not_le at hx,
      have h₁ := drop_len_lt (Pos g.fresh.1) hk hx,
      have h₂ := disjoint_fresh_of_disjoint hk hdis,

      

      have ihred := ih _ h₁ h₂ α,

      
    }

  }
end
/-
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

    rw [c_to_app, eval_xor_cnf_eq_eval_nxor, nxor.eval_append] at h,
    
    --have ihred := ih (L ++ [Pos (f 0)]) (dropn_len _ three_gt_one (not_le.mp hlen)) 
    --  (restriction_injective hinj) (res_disjoint hinj him),

    cases h3eval : nxor.eval α [a, b, c],
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
      { rw eval_xor_cnf_eq_eval_nxor,
        rw nxor.eval_append,
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
          rw [this, eval_xor_cnf_eq_eval_nxor, nxor.eval_append],
          rw nxor.eval_singleton,
          simp [nxor.eval_cons, literal.eval],
          rw ite_pos_of_lit _ _ hav_in, -- This is overly manual...
          rw ite_pos_of_lit _ _ hbv_in,
          rw ite_pos_of_lit _ _ hcv_in,
          rw ite_neg _ _ hf0_not_mem2,
          rw ← heqod (f 0) hf0_mem,
          simp [set_var],
          rw ← bxor_tt_right (literal.eval α c),
          simp only [← bool.bxor_assoc],
          rw bxor_tt_right,
          simp [nxor.eval_cons] at h3eval,
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

      rw eval_xor_cnf_eq_eval_nxor,
      rw eval_xor_cnf_eq_eval_nxor at h₁,
      rw eval_xor_cnf_eq_eval_nxor at ha₂,
      rw nxor.eval_append,
      rw nxor.eval_append at ha₂,
      cases heval : α₂ (f 0),
      { simp [literal.eval, heval] at ha₂,
        simp only [nxor.eval_cons, literal.eval, heval, hf0_eval] at h₁,
        rw nxor.eval_nil at h₁,
        rw bool.bxor_ff_right at h₁,
        simp only [← bool.bxor_assoc] at h₁, -- clean up manual
        rw bool.bnot_false at h₁,
        rw bxor_tt_right at h₁,
        simp at h₁,
        rw equiv_on_domain_for_xor heqod₂,
        simp [ha₂, nxor.eval_cons, h₁] },
      {
        simp [literal.eval, heval] at ha₂,
        simp only [nxor.eval_cons, literal.eval, heval, hf0_eval] at h₁,
        rw nxor.eval_nil at h₁,
        rw bool.bxor_ff_right at h₁,
        simp only [← bool.bxor_assoc] at h₁, -- clean up manual
        rw bool.bnot_true at h₁,
        rw bool.bxor_ff_right at h₁,
        simp at h₁,
        rw equiv_on_domain_for_xor heqod₂,
        simp [ha₂, nxor.eval_cons, h₁] } },
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
-/

end tseitin_xor