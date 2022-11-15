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

variables {V : Type*} [decidable_eq V] [inhabited V]

open assignment
open clause
open list
open nat
open distinct

def amk (k : nat) (l : list bool) : bool := l.count tt ≤ k

namespace amk

@[simp] theorem amk_nil (k : nat) : amk k [] = tt := rfl

@[simp] theorem amk_singleton_pos (k : nat) (b : bool) : amk (k + 1) [b] = tt :=
by { cases b; simp [amk, count_singleton'] }

protected def eval (k : nat) (τ : assignment V) (l : list (literal V)) : bool :=
  amk k (l.map (literal.eval τ))

variables (k : nat) (τ : assignment V) (l : list (literal V)) (lit : literal V)

@[simp] theorem eval_nil : amk.eval k τ [] = tt :=
by simp only [amk.eval, amk, count_nil, to_bool_true_eq_tt, zero_le, map_nil]

@[simp] theorem eval_singleton_pos : amk.eval (k + 1) τ [lit] = tt :=
by { cases h : lit.eval τ; simp [amk.eval, amk, count_singleton', h] }

@[simp] theorem eval_singleton_zero : 
  (amk.eval 0 τ [lit] = tt) ↔ lit.eval τ = ff :=
begin
  cases h : (lit.eval τ),
  { split,
    { tautology },
    { intro _, simp [amk.eval, amk, h] } },
  { split,
    { intro hamk,
      simp [amk.eval, amk, h] at hamk,
      contradiction },
    { intro h, contradiction } }
end

theorem eval_tt_of_ge_length {k : nat} {l : list (literal V)} :
  k ≥ length l → ∀ (τ : assignment V), amk.eval k τ l = tt :=
begin
  intros hk τ,
  simp [amk.eval, amk],
  have := count_le_length tt (map (literal.eval τ) l),
  rw length_map at this,
  exact le_trans this hk
end

theorem eval_cons_pos {k : nat} {τ : assignment V} {lit : literal V} : 
  lit.eval τ = tt → ∀ l, amk.eval (k + 1) τ (lit :: l) = amk.eval k τ l :=
assume hlit l, by simp [amk.eval, amk, hlit, succ_le_succ_iff]

theorem eval_cons_neg {k : nat} {τ : assignment V} {lit : literal V} :
  lit.eval τ = ff → ∀ l, amk.eval k τ (lit :: l) = amk.eval k τ l :=
assume hlit l, by simp [amk.eval, amk, hlit]

theorem eval_tt_of_le_of_eval_tt {τ : assignment V} {l : list (literal V)} 
  {k₁ k₂ : nat} : k₁ ≤ k₂ → amk.eval k₁ τ l = tt → amk.eval k₂ τ l = tt :=
begin
  simp only [amk.eval, amk, ge_iff_le, to_bool_iff],
  intros hk h₁,
  exact le_trans h₁ hk  
end

theorem eval_sublist {k : nat} {τ : assignment V} {l₁ l₂ : list (literal V)} :
  l₁ <+ l₂ → amk.eval k τ l₂ = tt → amk.eval k τ l₁ = tt :=
begin
  simp [amk.eval, amk],
  intros hs h, 
  exact le_trans (sublist.count_le (sublist.map (literal.eval τ) hs) tt) h
end

theorem eval_drop {k : nat} {τ : assignment V} {l : list (literal V)} :
  amk.eval k τ l = tt → ∀ (i : nat), amk.eval k τ (l.drop i) = tt :=
assume hamk i, eval_sublist (drop_sublist i l) hamk

theorem eval_take {k : nat} {τ : assignment V} {l : list (literal V)} :
  amk.eval k τ l = tt → ∀ (i : nat), amk.eval k τ (l.take i) = tt :=
assume hamk i, eval_sublist (take_sublist i l) hamk 

/-! # amz -/

theorem amz_of_amz_cons {τ : assignment V} {l : list (literal V)} {lit : literal V} :
  amk.eval 0 τ (lit :: l) = tt → amk.eval 0 τ l = tt :=
begin
  simp [amk.eval, amk], cases literal.eval τ lit; simp
end

-- The special case where k = 0 is handled
theorem amz_eval_tt_iff_forall_eval_ff :
  amk.eval 0 τ l = tt ↔ (∀ (lit : literal V), lit ∈ l → lit.eval τ = ff) :=
begin
  split,
  { simp [amk.eval, amk] },
  { intro h,
    rw [amk.eval, amk, to_bool_iff, le_zero_iff],
    apply count_eq_zero_of_not_mem,
    simpa }
end

-- Can be done with contrapose, somehow
theorem amz_eval_ff_iff_exists_eval_tt :
  amk.eval 0 τ l = ff ↔ (∃ (lit : literal V), lit ∈ l ∧ lit.eval τ = tt) :=
begin
  split,
  { contrapose, simp,
    exact (amz_eval_tt_iff_forall_eval_ff τ l).mpr },
  { contrapose, simp,
    exact (amz_eval_tt_iff_forall_eval_ff τ l).mp }
end

theorem eval_cons_pos_zero {τ : assignment V} {lit : literal V} :
  lit.eval τ = tt → ∀ l, amk.eval 0 τ (lit :: l) = ff :=
begin
  intros hlit l,
  apply (amz_eval_ff_iff_exists_eval_tt τ (lit :: l)).mpr,
  use [lit, mem_cons_self _ _, hlit]
end

/-! # back to general theorems -/

theorem eval_tail_pos {k i : nat} {τ : assignment V} {l : list (literal V)}
  {hi : i < length l} : (l.nth_le i hi).eval τ = tt →
  amk.eval (k + 1) τ (l.take (i + 1)) = amk.eval k τ (l.take i) :=
begin
  intro hamk,
  induction l with l₁ ls ih generalizing i k,
  { simp },
  { cases i,
    { simp },
    { rw [take, take],
      rw nth_le at hamk,
      rw [length, succ_lt_succ_iff] at hi,
      cases h₁ : (l₁.eval τ),
      { rw [eval_cons_neg h₁, eval_cons_neg h₁],
        exact ih hamk },
      { cases k,
        { rw eval_cons_pos_zero h₁, -- Can be tightened up
          rw eval_cons_pos h₁,
          by_contradiction,
          rw [eq_tt_eq_not_eq_ff, amz_eval_tt_iff_forall_eval_ff] at h,
          have : length (ls.take (i + 1)) = i + 1,
          { have h := length_take (i + 1) ls,
            have : min (i + 1) (length ls) = i + 1,
            { simp [succ_le_of_lt hi] },
            rw this at h,
            exact h },
          have hlen : i < length (ls.take (i + 1)),
          { rw this,
            exact lt_succ_self i },
          have hmem := nth_le_mem _ _ hlen,
          have : (ls.nth_le i _) = (ls.take (i.succ)).nth_le i hlen,
          { rw this at hlen,
            exact nth_le_take ls hi hlen },
          rw ← this at hmem,
          have hff := h _ hmem,
          have : literal.eval τ (ls.nth_le i hi) = tt,
          { assumption },
          rw this at hff,
          contradiction },
        { rw [eval_cons_pos h₁, eval_cons_pos h₁],
          exact ih hamk } } } }
end

theorem eval_tail_neg {k i : nat} {τ : assignment V} {l : list (literal V)}
  {hi : i < length l} : (l.nth_le i hi).eval τ = ff →
  amk.eval k τ (l.take (i + 1)) = amk.eval k τ (l.take i) :=
begin
  intro hamk,
  induction l with l₁ ls ih generalizing i k,
  { simp },
  { cases i,
    { simp at hamk, cases k; simp [hamk] },
    { rw [take, take],
      rw nth_le at hamk,
      rw [length, succ_lt_succ_iff] at hi,
      cases h₁ : (l₁.eval τ),
      { rw [eval_cons_neg h₁, eval_cons_neg h₁],
        exact ih hamk },
      { cases k,
        { rw [eval_cons_pos_zero h₁, eval_cons_pos_zero h₁] },
        { rw [eval_cons_pos h₁, eval_cons_pos h₁],
          exact ih hamk } } } }
end

-- Can probably be shortened with the correct order of cases
theorem exists_amk_split {k : nat} {τ : assignment V} {l : list (literal V)} : 
  amk.eval k τ l = tt → ∀ {k₁ k₂ : nat}, k₁ + k₂ = k → 
  ∃ {l₁ l₂ : list (literal V)}, l₁ ++ l₂ = l ∧
  amk.eval k₁ τ l₁ = tt ∧ amk.eval k₂ τ l₂ = tt :=
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
        rw (hamk _ (mem_cons_self lit₁ ls)) at hlit₁,
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

theorem eval_eq_amk_of_eqod {τ₁ τ₂ : assignment V} {l : list (literal V)} :
  ∀ (k : nat), (eqod τ₁ τ₂ (clause.vars l)) → amk.eval k τ₁ l = amk.eval k τ₂ l :=
begin
  intros k heqod,
  induction l with l ls ih generalizing k,
  { simp only [eval_nil] },
  { have := eval_eq_of_eqod_of_var_mem heqod (mem_vars_of_mem (mem_cons_self l ls)),
    cases h : (l.eval τ₁),
    { rw eval_cons_neg h,
      rw this at h,
      rw eval_cons_neg h,
      exact ih (eqod_subset (vars_subset_of_vars_cons _ _) heqod) k },
    { cases k,
      { rw eval_cons_pos_zero h,
        rw this at h,
        rw eval_cons_pos_zero h },
      { rw eval_cons_pos h,
        rw this at h,
        rw eval_cons_pos h,
        exact ih (eqod_subset (vars_subset_of_vars_cons _ _) heqod) k } } }
end

/-! # amo -/

theorem amo_eval_tt_iff_distinct_eval_ff_of_eval_tt 
  {τ : assignment V} {l : list (literal V)} :
  amk.eval 1 τ l = tt ↔ (∀ {lit₁ lit₂ : literal V}, 
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
          exact heval lit₂ hmem₂ },
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
              exact heval lit₂ hmem₂ } } } },
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