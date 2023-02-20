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

open assignment clause amk distinct
open list nat

variables {V : Type*} [decidable_eq V] [inhabited V]

def alk (k : nat) : constraint := λ l, l.count tt ≥ k

namespace alk

@[simp] theorem eval_zero : ∀ (τ : assignment V) (l : list (literal V)), 
  (alk 0).eval τ l = tt :=
assume τ l, by simp only [constraint.eval, alk, ge_iff_le, zero_le, to_bool_true_eq_tt]

@[simp] theorem eval_nil_ff_iff_pos {k : nat} :
  ∀ τ, ((alk k).eval τ ([] : list (literal V)) = ff ↔ k > 0) :=
assume τ, by simp [constraint.eval, alk, pos_iff_ne_zero]

@[simp] theorem eval_nil_tt_iff_zero {k : nat} :
  ∀ τ, ((alk k).eval τ ([] : list (literal V)) = tt ↔ k = 0) :=
assume τ, by simp [constraint.eval, alk]

variables {k : nat} {τ : assignment V} {lit : literal V} {l : list (literal V)}

theorem eval_cons_pos : lit.eval τ = tt → 
  ∀ l, (alk (k + 1)).eval τ (lit :: l) = (alk k).eval τ l :=
assume hlit l, by simp [constraint.eval, alk, hlit, succ_le_succ_iff]

theorem eval_cons_neg : lit.eval τ = ff → 
  ∀ l, (alk k).eval τ (lit :: l) = (alk k).eval τ l :=
assume hlit l, 
by simp only [constraint.eval, alk, hlit, map, count_cons_of_ne, ne.def, not_false_iff]

/-
theorem eval_tt_of_gt :
  (alk k).eval τ l = tt → ∀ ⦃j : nat⦄, j < k → (alk j).eval τ l = tt :=
begin
  intros halk j hj,
  sorry
end
-/

-- TODO: supply k as an explicit arg, or ∀ in conclusion
theorem eval_take_tail_pos {i : nat} {Hi : i < length l} : 
  (l.nth_le i Hi).eval τ = tt → 
  (alk (k + 1)).eval τ (l.take (i + 1)) = (alk k).eval τ (l.take i) :=
begin
  intro hl,
  induction i with i ih generalizing l k,
  { rw nth_le_zero at hl,
    simp [take_one_of_ne_nil (ne_nil_of_length_pos Hi), hl, constraint.eval, alk] },
  { rcases exists_cons_of_ne_nil (ne_nil_of_length_pos (pos_of_gt Hi)) with ⟨l₁, ls, rfl⟩,
    rw nth_le at hl,
    cases h₁ : l₁.eval τ,
    { simp only [take, eval_cons_neg h₁, ih hl] },
    { cases k,
      { simp [constraint.eval, alk, h₁, succ_le_succ_iff] },
      { simp [take, eval_cons_pos h₁],
        exact ih hl } } }
end

theorem eval_take_tail_neg {i : nat} {Hi : i < length l} :
  (l.nth_le i Hi).eval τ = ff →
  (alk k).eval τ (l.take (i + 1)) = (alk k).eval τ (l.take i) :=
begin
  intro hl,
  induction i with i ih generalizing l k,
  { rw nth_le_zero at hl,
    simp [take_one_of_ne_nil (ne_nil_of_length_pos Hi), hl, constraint.eval, alk] },
  { rcases exists_cons_of_ne_nil (ne_nil_of_length_pos (pos_of_gt Hi)) with ⟨l₁, ls, rfl⟩,
    rw nth_le at hl,
    cases h₁ : l₁.eval τ,
    { simp [take, eval_cons_neg h₁, ih hl] },
    { cases k,
      { simp [take, constraint.eval, alk] },
      { simp [take, eval_cons_pos h₁, ih hl] } } }
end

theorem alo_eval_tt_iff_exists_eval_tt :
  (alk 1).eval τ l = tt ↔ ∃ {lit : literal V}, lit ∈ l ∧ lit.eval τ = tt :=
begin
  induction l with lit₁ ls ih,
  { simp only [eval_nil_tt_iff_zero, nat.one_ne_zero, not_mem_nil, false_and, exists_false] },
  { cases hlit₁ : lit₁.eval τ,
    { rw eval_cons_neg hlit₁,
      split,
      { intro h,
        rcases ih.mp h with ⟨lit, hmem, heval⟩,
        exact ⟨lit, mem_cons_of_mem _ hmem, heval⟩ },
      { rintro ⟨lit, hmem, heval⟩,
        rcases eq_or_mem_of_mem_cons hmem with (rfl | hmem),
        { rw hlit₁ at heval, contradiction },
        { exact ih.mpr ⟨lit, hmem, heval⟩ } } },
    { split,
      { intro _, use [lit₁, mem_cons_self _ _, hlit₁] },
      { intro _, rw eval_cons_pos hlit₁, exact eval_zero τ ls } } }
end

theorem amo_take_of_tt {i : nat} (Hi : i < length l) :
  (l.nth_le i Hi).eval τ = tt → (alk 1).eval τ (l.take (i + 1)) = tt :=
assume ht, eval_zero τ l ▸ eval_take_tail_pos ht

theorem alo_take_tail {i : nat} (Hi : i < length l) :
  (alk 1).eval τ (l.take (i + 1)) = tt →
  ((l.nth_le i Hi).eval τ = tt ∨ (alk 1).eval τ (l.take i) = tt) :=
begin
  intro hlk,
  cases hl : (l.nth_le i Hi).eval τ,
  { rw eval_take_tail_neg hl at hlk,
    exact or.inr hlk },
  { exact or.inl rfl }
end

theorem eval_tt_of_ge_of_eval_tt {k₁ k₂ : nat} : k₁ ≥ k₂ → 
  (alk k₁).eval τ l = tt → (alk k₂).eval τ l = tt :=
begin
  simp only [constraint.eval, alk, ge_iff_le, to_bool_iff],
  intros hk h₁,
  exact le_trans hk h₁
end

theorem eval_tt_of_sublist_of_eval_tt {l₁ l₂ : list (literal V)} :
  l₁ <+ l₂ → (alk k).eval τ l₁ = tt → (alk k).eval τ l₂ = tt :=
begin
  simp [constraint.eval, alk],
  intros hls h₁,
  exact le_trans h₁ (sublist.count_le (sublist.map (literal.eval τ) hls) tt)
end

theorem eval_take_succ_tt_of_eval_take_tt {i k : nat} :
  (alk k).eval τ (l.take i) = tt → (alk k).eval τ (l.take (i + 1)) = tt :=
λ h, eval_tt_of_sublist_of_eval_tt (take_sublist_of_le (le_succ i) l) h

theorem amk_alk_take {k : nat} {l : list (literal V)} {i : nat} :
  i ≤ length l → ∀ {τ : assignment V}, (alk k).eval τ (l.take i) = tt →
  (amk k).eval τ l = tt → (amk 0).eval τ (l.drop i) = tt :=
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
  (amk k).eval τ l = !((alk (k + 1)).eval τ l) :=
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
  (alk (k + 1)).eval τ l = tt → ∃ {i : nat} (Hi : i < length l),
  (amk 0).eval τ (l.take (i - 1)) = tt ∧ (l.nth_le i Hi).eval τ = tt ∧
  (alk k).eval τ (l.drop (i + 1)) = tt :=
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
  (amk j).eval τ l = tt → ∀ {k}, j < k → (alk k).eval τ l = ff :=
begin
  induction l with l₁ ls ih generalizing j,
  { simp, intros k hk, exact pos_of_gt hk },
  { intros hmk k hk,
    cases j,
    { have ihred := ih (amz_of_amz_cons hmk) hk,
      rw amz_eval_tt_iff_forall_eval_ff at hmk,
      rw eval_cons_neg (hmk (mem_cons_self _ _)),
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

-- Since the at-least-one encoding is so simple, we prove it here
section direct_alo

open encoding

def direct_alo : enc_fn V := λ l g, ⟨[l], g⟩

theorem direct_alo_is_wb : is_wb (direct_alo : enc_fn V) :=
begin
  intros l g hdis, simp [direct_alo]
end

theorem direct_alo_encodes_alo : encodes (alk 1) (direct_alo : enc_fn V) :=
begin
  split,
  {
    intros l g hdis τ,
    rw alo_eval_tt_iff_exists_eval_tt,
    split,
    { intro h,
      use τ, split,
      { simp [direct_alo, eval_tt_iff_exists_literal_eval_tt, h] },
      { refl } },
    {
      rintro ⟨σ, hs, hagree_on⟩,
      simp [direct_alo, eval_tt_iff_exists_literal_eval_tt] at hs,
      rcases hs with ⟨lit, hmem, hlit⟩,
      rw ← eval_eq_of_agree_on_of_var_mem hagree_on (mem_vars_of_mem hmem) at hlit,
      exact ⟨lit, hmem, hlit⟩ } },
  { exact direct_alo_is_wb }
end

end direct_alo

end alk