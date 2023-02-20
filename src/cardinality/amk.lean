/-
This file defines the at-most-k Boolean cardinality constraint.

Authors: Cayden Codel, Jeremy Avigad, Marijn Heule
Carnegie Mellon University
-/

import data.list.basic
import cnf.literal
import cnf.assignment
import cnf.clause
import cardinality.distinct
import cnf.encoding

variables {V : Type*} [decidable_eq V] [inhabited V]

open assignment
open clause
open list
open nat
open distinct

def amk (k : nat) : constraint := λ (l : list bool), l.count tt ≤ k

namespace amk

@[simp] theorem amk_nil (k : nat) : amk k [] = tt := rfl

@[simp] theorem amk_singleton_pos (k : nat) (b : bool) : amk (k + 1) [b] = tt :=
by { cases b; simp [amk, count_singleton'] }

variables (k : nat) (τ : assignment V) (l : list (literal V)) (lit : literal V)

@[simp] theorem eval_nil : (amk k).eval τ [] = tt :=
by simp only [constraint.eval, amk, count_nil, to_bool_true_eq_tt, zero_le, map_nil]

@[simp] theorem eval_singleton_pos : (amk (k + 1)).eval τ [lit] = tt :=
by { cases h : lit.eval τ; simp [constraint.eval, amk, count_singleton', h] }

@[simp] theorem eval_singleton_zero : ((amk 0).eval τ [lit] = tt) ↔ lit.eval τ = ff :=
begin
  cases h : (lit.eval τ),
  { split,
    { tautology },
    { intro _, simp [constraint.eval, amk, h] } },
  { split,
    { intro hamk,
      simp [constraint.eval, amk, h] at hamk,
      contradiction },
    { intro h, contradiction } }
end

theorem eval_tt_of_ge_length {k : nat} {l : list (literal V)} :
  k ≥ length l → ∀ (τ : assignment V), (amk k).eval τ l = tt :=
begin
  intros hk τ,
  simp [constraint.eval, amk],
  have := count_le_length tt (map (literal.eval τ) l),
  rw length_map at this,
  exact le_trans this hk
end

theorem eval_cons_pos {k : nat} {τ : assignment V} {lit : literal V} : 
  lit.eval τ = tt → ∀ l, (amk (k + 1)).eval τ (lit :: l) = (amk k).eval τ l :=
assume hlit l, by simp [constraint.eval, amk, hlit, succ_le_succ_iff]

theorem eval_cons_neg {τ : assignment V} {lit : literal V} :
  lit.eval τ = ff → ∀ k l, (amk k).eval τ (lit :: l) = (amk k).eval τ l :=
assume hlit l, by simp [constraint.eval, amk, hlit]

theorem eval_tt_of_le_of_eval_tt {τ : assignment V} {l : list (literal V)} 
  {k₁ k₂ : nat} : k₁ ≤ k₂ → (amk k₁).eval τ l = tt → (amk k₂).eval τ l = tt :=
begin
  simp only [constraint.eval, amk, ge_iff_le, to_bool_iff],
  intros hk h₁,
  exact le_trans h₁ hk  
end

theorem eval_sublist {k : nat} {τ : assignment V} {l₁ l₂ : list (literal V)} :
  l₁ <+ l₂ → (amk k).eval τ l₂ = tt → (amk k).eval τ l₁ = tt :=
begin
  simp [constraint.eval, amk],
  intros hs h, 
  exact le_trans (sublist.count_le (sublist.map (literal.eval τ) hs) tt) h
end

theorem eval_drop {k : nat} {τ : assignment V} {l : list (literal V)} :
  (amk k).eval τ l = tt → ∀ (i : nat), (amk k).eval τ (l.drop i) = tt :=
assume hamk i, eval_sublist (drop_sublist i l) hamk

theorem eval_take {k : nat} {τ : assignment V} {l : list (literal V)} :
  (amk k).eval τ l = tt → ∀ (i : nat), (amk k).eval τ (l.take i) = tt :=
assume hamk i, eval_sublist (take_sublist i l) hamk 

theorem eval_take_tail_pos {τ : assignment V} {l : list (literal V)} {i : nat} {Hi : i < length l} : 
  (l.nth_le i Hi).eval τ = tt → ∀ (k : nat),
  (amk (k + 1)).eval τ (l.take (i + 1)) = (amk k).eval τ (l.take i) :=
begin
  intros hl k,
  induction i with i ih generalizing l k,
  { rw nth_le_zero at hl,
    simp [take_one_of_ne_nil (ne_nil_of_length_pos Hi), hl, constraint.eval, amk] },
  { rcases exists_cons_of_ne_nil (ne_nil_of_length_pos (pos_of_gt Hi)) with ⟨l₁, ls, rfl⟩,
    rw nth_le at hl,
    cases h₁ : l₁.eval τ,
    { simp only [take, eval_cons_neg h₁, ih _ hl] },
    { cases k,
      { simp [constraint.eval, amk, h₁, succ_le_succ_iff],
        simp at Hi,
        have Hi' := (succ_lt_succ_iff.mp Hi),
        use [ls.nth_le _ Hi', nth_le_mem_take_of_lt Hi' (lt_succ_self i), hl] },
      { simp [take, eval_cons_pos h₁], exact ih _ hl } } }
end

theorem eval_take_tail_neg {τ : assignment V} {l : list (literal V)} {i : nat} {Hi : i < length l} :
  (l.nth_le i Hi).eval τ = ff → ∀ (k : nat),
  (amk k).eval τ (l.take (i + 1)) = (amk k).eval τ (l.take i) :=
begin
  intros hl k,
  induction i with i ih generalizing l k,
  { rw nth_le_zero at hl,
    simp [take_one_of_ne_nil (ne_nil_of_length_pos Hi), hl, constraint.eval, amk] },
  { rcases exists_cons_of_ne_nil (ne_nil_of_length_pos (pos_of_gt Hi)) with ⟨l₁, ls, rfl⟩,
    rw nth_le at hl,
    cases h₁ : l₁.eval τ,
    { simp [take, eval_cons_neg h₁, ih _ hl] },
    { cases k,
      { simp [take, constraint.eval, amk, h₁] },
      { simp [take, eval_cons_pos h₁, ih _ hl] } } }
end

theorem eval_tt_of_sublist_of_eval_tt {k : nat} {τ : assignment V} {l₁ l₂ : list (literal V)} :
  l₁ <+ l₂ → (amk k).eval τ l₂ = tt → (amk k).eval τ l₁ = tt :=
begin
  simp [constraint.eval, amk],
  intros hls h₁,
  exact le_trans (sublist.count_le (sublist.map (literal.eval τ) hls) tt) h₁
end

theorem eval_take_succ_tt_of_eval_take_tt {i k : nat} :
  (amk k).eval τ (l.take (i + 1)) = tt → (amk k).eval τ (l.take i) = tt :=
λ h, eval_tt_of_sublist_of_eval_tt (take_sublist_of_le (le_succ i) l) h

/-! # amz -/

theorem amz_of_amz_cons {τ : assignment V} {l : list (literal V)} {lit : literal V} :
  (amk 0).eval τ (lit :: l) = tt → (amk 0).eval τ l = tt :=
begin
  simp [constraint.eval, amk], cases literal.eval τ lit; simp
end

-- The special case where k = 0 is handled
theorem amz_eval_tt_iff_forall_eval_ff {τ} {l} :
  (amk 0).eval τ l = tt ↔ (∀ ⦃lit : literal V⦄, lit ∈ l → lit.eval τ = ff) :=
begin
  split,
  { simp [constraint.eval, amk] },
  { intro h,
    rw [constraint.eval, amk, to_bool_iff, le_zero_iff],
    apply count_eq_zero_of_not_mem,
    simpa }
end

-- Can be done with contrapose, somehow
theorem amz_eval_ff_iff_exists_eval_tt :
  (amk 0).eval τ l = ff ↔ (∃ (lit : literal V), lit ∈ l ∧ lit.eval τ = tt) :=
begin
  split,
  { contrapose, simp, exact amz_eval_tt_iff_forall_eval_ff.mpr },
  { contrapose, simp, exact amz_eval_tt_iff_forall_eval_ff.mp }
end

theorem eval_cons_pos_zero {τ : assignment V} {lit : literal V} :
  lit.eval τ = tt → ∀ l, (amk 0).eval τ (lit :: l) = ff :=
begin
  intros hlit l,
  apply (amz_eval_ff_iff_exists_eval_tt τ (lit :: l)).mpr,
  use [lit, mem_cons_self _ _, hlit]
end

-- Can probably be shortened with the correct order of cases
theorem exists_amk_split {k : nat} {τ : assignment V} {l : list (literal V)} : 
  (amk k).eval τ l = tt → ∀ {k₁ k₂ : nat}, k₁ + k₂ = k → 
  ∃ {l₁ l₂ : list (literal V)}, l₁ ++ l₂ = l ∧
  (amk k₁).eval τ l₁ = tt ∧ (amk k₂).eval τ l₂ = tt :=
begin
  intros hamk k₁ k₂ hks,
  induction l with lit₁ ls ih generalizing k k₁ k₂,
  { use [[], []],
    simp },
  { cases k,
    { cases hlit₁ : (literal.eval τ lit₁),
      { rw eval_cons_neg hlit₁ at hamk,
        rcases ih hamk hks with ⟨l₁, l₂, hls, hl₁, hl₂⟩,
        use [(lit₁ :: l₁), l₂],
        simp [hls, eval_cons_neg hlit₁, hl₁, hl₂] },
      { rw [amz_eval_tt_iff_forall_eval_ff] at hamk,
        rw (hamk (mem_cons_self lit₁ ls)) at hlit₁,
        contradiction } },
    { cases k₁,
      { rw zero_add at hks, subst hks,
        use [[], lit₁ :: ls],
        simpa },
      { cases hlit₁ : (literal.eval τ lit₁),
        { rw eval_cons_neg hlit₁ at hamk,
          rcases ih hamk hks with ⟨l₁, l₂, hls, hl₁, hl₂⟩,
          use [(lit₁ :: l₁), l₂],
          simp [hls, eval_cons_neg hlit₁, hl₁, hl₂] },
        { rw succ_add at hks,
          rw eval_cons_pos hlit₁ at hamk,
          rcases ih hamk (succ.inj hks) with ⟨l₁, l₂, hls, hl₁, hl₂⟩,
          use [(lit₁ :: l₁), l₂],
          simp [hls, eval_cons_pos hlit₁, hl₁, hl₂] } } } }
end

theorem eval_eq_of_agree_on {τ₁ τ₂ : assignment V} {l : list (literal V)} :
  ∀ (k : nat), (agree_on τ₁ τ₂ (clause.vars l)) → (amk k).eval τ₁ l = (amk k).eval τ₂ l :=
begin
  intros k hagree_on,
  induction l with l ls ih generalizing k,
  { simp only [eval_nil] },
  { have := eval_eq_of_agree_on_of_var_mem hagree_on (mem_vars_of_mem (mem_cons_self l ls)),
    cases h : (l.eval τ₁),
    { rw eval_cons_neg h,
      rw this at h,
      rw eval_cons_neg h,
      exact ih (agree_on_subset (vars_subset_of_vars_cons _ _) hagree_on) k },
    { cases k,
      { rw eval_cons_pos_zero h,
        rw this at h,
        rw eval_cons_pos_zero h },
      { rw eval_cons_pos h,
        rw this at h,
        rw eval_cons_pos h,
        exact ih (agree_on_subset (vars_subset_of_vars_cons _ _) hagree_on) k } } }
end

/-! # amo -/

theorem amo_eval_tt_iff_distinct_eval_ff_of_eval_tt 
  {τ : assignment V} {l : list (literal V)} :
  (amk 1).eval τ l = tt ↔ (∀ {lit₁ lit₂ : literal V}, 
  distinct lit₁ lit₂ l → lit₁.eval τ = tt → lit₂.eval τ = ff) :=
begin
  induction l with l₁ ls ih,
  { split,
    { intros _ lit₁ lit₂ hdis,
      exact absurd hdis (not_distinct_nil _ _) },
    { rw eval_nil, tautology } },
  { cases ls with l₂ ls,
    { split,
      { intros _ lit₁ lit₂ hdis,
        exact absurd hdis (not_distinct_singleton _ _ _) },
      { rw eval_singleton_pos, tautology } },
    { split,
      { intros heval lit₁ lit₂ hdis h₁,
        have hmem₂ := mem_tail_of_distinct_cons hdis,
        rcases hdis with ⟨i, j, hi, hj, hij, hil, hjl⟩,
        cases i,
        { rw nth_le at hil,
          rw [hil, eval_cons_pos h₁, amz_eval_tt_iff_forall_eval_ff] at heval,
          exact heval hmem₂ },
        { cases j,
          { linarith },
          { have : distinct lit₁ lit₂ (l₂ :: ls),
            { rw [length, succ_lt_succ_iff] at hi hj,
              rw succ_lt_succ_iff at hij,
              rw nth_le at hil hjl,
              exact ⟨i, j, hi, hj, hij, hil, hjl⟩ },
            cases h : (literal.eval τ l₁),
            { rw eval_cons_neg h at heval,
              exact ih.mp heval this h₁ },
            { rw [eval_cons_pos h, amz_eval_tt_iff_forall_eval_ff] at heval,
              exact heval hmem₂ } } } },
      { intro h,
        cases h₁ : (literal.eval τ l₁),
        { rw eval_cons_neg h₁,
          apply ih.mpr,
          intros lit₁ lit₂ hdis' h₁',
          exact h (distinct_cons_of_distinct l₁ hdis') h₁' },
        { rw [eval_cons_pos h₁, amz_eval_tt_iff_forall_eval_ff],
          intros x hx,
          exact h (distinct_cons_of_mem l₁ hx) h₁ } } } }
end

end amk