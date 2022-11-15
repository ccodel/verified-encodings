/-
The at-least-k boolean function.

Authors: Cayden Codel, Jeremy Avigad, Marijn Heule
Carnegie Mellon University
-/

import data.list.basic
import cnf.literal
import cnf.assignment
import cnf.clause
import cardinality.distinct
import cardinality.amk

variables {V : Type*} [decidable_eq V] [inhabited V]

open assignment
open clause
open list
open nat
open distinct
open amk

def alk (k : nat) (l : list bool) : bool := l.count tt ≥ k

namespace alk

protected def eval (k : nat) (τ : assignment V) (l : list (literal V)) : bool :=
  alk k (l.map (literal.eval τ))

@[simp] theorem eval_zero : ∀ (τ : assignment V) (l : list (literal V)), 
  alk.eval 0 τ l = tt :=
assume τ l, by simp only [alk.eval, alk, ge_iff_le, zero_le, to_bool_true_eq_tt]

@[simp] theorem eval_nil_ff_iff_pos {k : nat} :
  ∀ τ, (alk.eval k τ ([] : list (literal V)) = ff ↔ k > 0) :=
assume τ, by simp [alk.eval, alk, pos_iff_ne_zero]

@[simp] theorem eval_nil_tt_iff_zero {k : nat} :
  ∀ τ, (alk.eval k τ ([] : list (literal V)) = tt ↔ k = 0) :=
assume τ, by simp [alk.eval, alk]

variables {k : nat} {τ : assignment V} {lit : literal V} {l : list (literal V)}

theorem eval_cons_pos : lit.eval τ = tt → 
  ∀ l, alk.eval (k + 1) τ (lit :: l) = alk.eval k τ l :=
assume hlit l, by simp [alk.eval, alk, hlit, succ_le_succ_iff]

theorem eval_cons_neg : lit.eval τ = ff → 
  ∀ l, alk.eval k τ (lit :: l) = alk.eval k τ l :=
assume hlit l, by simp [alk.eval, alk, hlit]

theorem eval_take_tail_pos {i : nat} (Hi : i < length l) : 
  (l.nth_le i Hi).eval τ = tt → 
  alk.eval (k + 1) τ (l.take (i + 1)) = alk.eval k τ (l.take i) :=
begin
  intro hl,
  induction i with i ih generalizing l k,
  { rw nth_le_zero at hl,
    simp [take_one_of_ne_nil (ne_nil_of_length_pos Hi), hl, alk.eval, alk] },
  { rcases exists_cons_of_ne_nil (ne_nil_of_length_pos (pos_of_gt Hi)) with ⟨l₁, ls, rfl⟩,
    rw nth_le at hl,
    cases h₁ : l₁.eval τ,
    { simp only [take, eval_cons_neg h₁, ih (succ_lt_succ_iff.mp Hi) hl] },
    { cases k,
      { simp [alk.eval, alk, h₁, succ_le_succ_iff] },
      { simp [take, eval_cons_pos h₁],
        exact ih (succ_lt_succ_iff.mp Hi) hl } } }
end

theorem eval_take_tail_neg {i : nat} (Hi : i < length l) :
  (l.nth_le i Hi).eval τ = ff →
  alk.eval k τ (l.take (i + 1)) = alk.eval k τ (l.take i) :=
begin
  intro hl,
  induction i with i ih generalizing l k,
  { rw nth_le_zero at hl,
    simp [take_one_of_ne_nil (ne_nil_of_length_pos Hi), hl, alk.eval, alk] },
  { rcases exists_cons_of_ne_nil (ne_nil_of_length_pos (pos_of_gt Hi)) with ⟨l₁, ls, rfl⟩,
    rw nth_le at hl,
    cases h₁ : l₁.eval τ,
    { simp [take, eval_cons_neg h₁, ih (succ_le_succ_iff.mp Hi) hl] },
    { cases k,
      { simp [take, alk.eval, alk] },
      { simp [take, eval_cons_pos h₁,ih (succ_le_succ_iff.mp Hi) hl] } } }
end

theorem amo_take_of_tt {i : nat} (Hi : i < length l) :
  (l.nth_le i Hi).eval τ = tt → alk.eval 1 τ (l.take (i + 1)) = tt :=
assume ht, eval_zero τ l ▸ eval_take_tail_pos Hi ht

theorem alo_take_tail {i : nat} (Hi : i < length l) :
  alk.eval 1 τ (l.take (i + 1)) = tt →
  ((l.nth_le i Hi).eval τ = tt ∨ alk.eval 1 τ (l.take i) = tt) :=
begin
  intro hlk,
  cases hl : (l.nth_le i Hi).eval τ,
  { rw eval_take_tail_neg Hi hl at hlk,
    exact or.inr hlk },
  { exact or.inl rfl }
end

theorem eval_tt_of_ge_of_eval_tt {k₁ k₂ : nat} : k₁ ≥ k₂ → 
  alk.eval k₁ τ l = tt → alk.eval k₂ τ l = tt :=
begin
  simp only [alk.eval, alk, ge_iff_le, to_bool_iff],
  intros hk h₁,
  exact le_trans hk h₁
end

theorem eval_tt_of_sublist_of_eval_tt {l₁ l₂ : list (literal V)} :
  l₁ <+ l₂ → alk.eval k τ l₁ = tt → alk.eval k τ l₂ = tt :=
begin
  simp [alk.eval, alk],
  intros hls h₁,
  exact le_trans h₁ (sublist.count_le (sublist.map (literal.eval τ) hls) tt)
end

theorem amk_alk_take {k : nat} {l : list (literal V)} {i : nat} :
  i ≤ length l → ∀ {τ : assignment V}, alk.eval k τ (l.take i) = tt →
  amk.eval k τ l = tt → amk.eval 0 τ (l.drop i) = tt :=
begin
  intros hi τ htake hamk,
  induction l with l₁ ls ih generalizing k i,
  { simp only [drop_eq_nil_of_le, length, zero_le, amk.eval_nil] },
  { cases i,
    { simp at htake, subst htake,
      rw drop,
      exact hamk },
    { cases k,
      { exact eval_drop hamk _ },
      { rw [length, succ_le_succ_iff] at hi,
        cases hl₁ : (l₁.eval τ),
        { rw [take, eval_cons_neg hl₁] at htake,
          rw amk.eval_cons_neg hl₁ at hamk,
          exact ih hi htake hamk },
        { rw [take, eval_cons_pos hl₁] at htake,
          rw amk.eval_cons_pos hl₁ at hamk,
          exact ih hi htake hamk } } } }
end

theorem amk_eval_eq_alk_succ_eval (k : nat) (τ : assignment V) (l : list (literal V)) :
  amk.eval k τ l = !(alk.eval (k + 1) τ l) :=
begin
  induction l with l₁ ls ih generalizing k,
  { apply symm, simp },
  { cases h₁ : l₁.eval τ,
    { rw [amk.eval_cons_neg h₁, alk.eval_cons_neg h₁],
      exact ih k },
    { cases k,
      { rw [amk.eval_cons_pos_zero h₁, alk.eval_cons_pos h₁, eval_zero],
        exact bool.bnot_tt.symm },
      { rw [amk.eval_cons_pos h₁, alk.eval_cons_pos h₁],
        exact ih k } } }
end

theorem alk_split {k : nat} {l : list (literal V)} {τ : assignment V} :
  alk.eval (k + 1) τ l = tt → ∃ {i : nat} (Hi : i < length l),
  amk.eval 0 τ (l.take (i - 1)) = tt ∧ (l.nth_le i Hi).eval τ = tt ∧
  alk.eval k τ (l.drop (i + 1)) = tt :=
begin
  intro halk,
  induction l with l₁ ls ih generalizing k,
  { simp at halk |-, assumption },
  { cases h₁ : l₁.eval τ,
    { rw eval_cons_neg h₁ at halk,
      rcases ih halk with ⟨i, Hi, htake, he, hdrop⟩,
      use i + 1,
      simp [Hi, hdrop],
      cases i,
      { simpa },
      { simp at htake, simpa [amk.eval_cons_neg h₁, htake] } },
    { rw eval_cons_pos h₁ at halk, use 0, simpa [h₁] } }
end

theorem alk_of_amk_of_gt {j : nat} {l : list (literal V)} {τ : assignment V} :
  amk.eval j τ l = tt → ∀ {k}, j < k → alk.eval k τ l = ff :=
begin
  induction l with l₁ ls ih generalizing j,
  { simp, intros k hk, exact pos_of_gt hk },
  { intros hmk k hk,
    cases j,
    { have ihred := ih (amz_of_amz_cons hmk) hk,
      rw amz_eval_tt_iff_forall_eval_ff at hmk,
      rw eval_cons_neg (hmk l₁ (mem_cons_self _ _)),
      exact ihred },
    { cases hl₁ : l₁.eval τ,
      { rw amk.eval_cons_neg hl₁ at hmk,
        rw eval_cons_neg hl₁,
        exact ih hmk hk },
      { cases k with k,
        { linarith },
        { rw amk.eval_cons_pos hl₁ at hmk,
          rw eval_cons_pos hl₁,
          exact ih hmk (succ_lt_succ_iff.mp hk) } } } }
end

/-
theorem alk_or_amk_pred_of_amk {k : nat} {l : list (literal V)} {τ : assignment V} :
  amk.eval (k + 1) τ l = tt → alk.eval (k + 1) τ l = tt ∨ amk.eval k τ l = tt :=
begin
  sorry
end
-/

end alk