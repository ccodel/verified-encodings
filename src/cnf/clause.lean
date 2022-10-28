/-
This file contains the definition of a Boolean (disjunctive) clause.
This particular implementation has clauses as lists.

Authors: Cayden Codel, Jeremy Avigad, Marijn Heule
Carnegie Mellon Univeristy
-/

import cnf.literal
import cnf.assignment
import basic

import data.list.basic

universe u

-- Represents the parametric type of the variable stored in the literal
variables {V : Type*}

/- Disjunctive clauses are lists of literals, joined by logical ORs. -/
def clause (V : Type*) := list (literal V)

-- Note that the above definition allows for duplication of literals, whereas
-- a set definition would not. Lists also allow for computable functions,
-- while Lean sets are noncomputable by default

namespace clause

open function
open literal
open list

/-! # Properties -/

-- Many of these properties follow directly from lists

instance [inhabited V] : inhabited (clause V) := ⟨[arbitrary (literal V)]⟩

instance has_decidable_eq [decidable_eq V] : decidable_eq (clause V)
| []        []        := is_true rfl
| (a :: as) []        := is_false (λ h, list.no_confusion h)
| []        (b :: bs) := is_false (λ h, list.no_confusion h)
| (a :: as) (b :: bs) :=
  match (literal.decidable_eq V) a b with
  | is_true hab  :=
    match has_decidable_eq as bs with
    | is_true h := is_true (eq.subst hab (eq.subst h rfl))
    | is_false hf := is_false (λ h, list.no_confusion h (λ _ ha, absurd ha hf))
    end
  | is_false hf := is_false (λ h, list.no_confusion h (λ hab _, absurd hab hf))
  end

instance : has_mem (literal V) (clause V) := ⟨list.mem⟩
instance : has_emptyc (clause V) := ⟨list.nil⟩ -- Refactor empty into [] below?
instance [decidable_eq V] : has_union (clause V) := ⟨list.union⟩
instance [decidable_eq V] : has_inter (clause V) := ⟨list.inter⟩
instance : has_singleton (literal V) (clause V) := ⟨λ l, [l]⟩ 
instance [decidable_eq V] : has_insert (literal V) (clause V) := ⟨list.insert⟩
instance : has_append (clause V) := ⟨list.append⟩
instance : has_subset (clause V) := ⟨list.subset⟩
instance [has_repr V] : has_repr (clause V) := ⟨list.repr⟩

instance [decidable_eq V] (l : literal V) (c : clause V) : decidable (l ∈ c) :=
by apply_instance

/-! # eval -/
section eval

variables (τ : assignment V) (l : literal V) (c c₁ c₂ : clause V)

protected def eval : bool := c.foldr (λ l b, b || (l.eval τ)) ff

@[simp] theorem eval_nil : clause.eval τ [] = ff := rfl

@[simp] theorem eval_singleton : clause.eval τ [l] = l.eval τ :=
by simp only [clause.eval, foldr, ff_bor]

@[simp] theorem eval_cons : clause.eval τ (l :: c) = (l.eval τ) || (c.eval τ) :=
by simp only [clause.eval, foldr, bool.bor_comm]

theorem eval_append : clause.eval τ (c₁ ++ c₂) = c₁.eval τ || c₂.eval τ :=
begin
  unfold clause.eval,
  rw foldr_append,
  cases foldr (λ l b, b || literal.eval τ l) ff c₂,
  { rw bor_ff },
  { rw [bor_tt, foldr_bor_tt] }
end

theorem eval_tt_iff_exists_literal_eval_tt {τ : assignment V} {c : clause V} : 
  c.eval τ = tt ↔ ∃ l, l ∈ c ∧ literal.eval τ l = tt :=
begin
  induction c with l ls ih,
  { simp only [eval_nil, not_mem_nil, false_and, exists_false] },
  { simp only [eval_cons, bor_eq_true_eq_eq_tt_or_eq_tt, mem_cons_iff],
    split,
    { rintros (h | h),
      { use [l, or.inl rfl, h] },
      { rcases ih.mp h with ⟨l₂, hl, he⟩,
        use [l₂, mem_cons_of_mem l hl, he] } },
    { rintros ⟨l₂, (rfl | hl), he⟩,
      { exact or.inl he },
      { exact or.inr (ih.mpr ⟨l₂, hl, he⟩) } } }
end

theorem eval_ff_iff_forall_literal_eval_ff {τ : assignment V} {c : clause V} : 
  clause.eval τ c = ff ↔ ∀ l, l ∈ c → literal.eval τ l = ff :=
begin
  induction c with l ls ih,
  { simp only [eval_nil, eq_self_iff_true, not_mem_nil, is_empty.forall_iff, implies_true_iff] },
  { simp only [eval_cons, bor_eq_false_eq_eq_ff_and_eq_ff, mem_cons_iff, 
      forall_eq_or_imp, and.congr_right_iff],
    intro _, exact ih }
end

theorem eval_tautology {c : clause V} {l : literal V} : 
  l ∈ c → l.flip ∈ c → ∀ (τ : assignment V), clause.eval τ c = tt :=
begin
  intros hl hlf τ,
  apply eval_tt_iff_exists_literal_eval_tt.mpr,
  cases h : (literal.eval τ l),
  { exact ⟨l.flip, hlf, eval_flip_of_eval h⟩ },
  { exact ⟨l, hl, h⟩ }
end

theorem eval_tt_of_subset_eval_tt {τ : assignment V} {c₁ c₂ : clause V} :
  c₁ ⊆ c₂ → clause.eval τ c₁ = tt → clause.eval τ c₂ = tt :=
begin
  intros h₁ h₂,
  apply eval_tt_iff_exists_literal_eval_tt.mpr,
  rcases eval_tt_iff_exists_literal_eval_tt.mp h₂ with ⟨l, hl, he⟩,
  exact ⟨l, h₁ hl, he⟩
end

theorem eval_ff_of_superset_eval_ff {τ : assignment V} {c₁ c₂ : clause V} :
  c₁ ⊆ c₂ → clause.eval τ c₂ = ff → clause.eval τ c₁ = ff :=
begin
  intros h₁ h₂,
  apply eval_ff_iff_forall_literal_eval_ff.mpr,
  intros l hl,
  exact (eval_ff_iff_forall_literal_eval_ff.mp h₂) l (h₁ hl)
end

theorem eval_tt_of_sublist_eval_tt {τ : assignment V} {c₁ c₂ : clause V} :
  c₁ <+ c₂ → clause.eval τ c₁ = tt → clause.eval τ c₂ = tt :=
assume h₁, eval_tt_of_subset_eval_tt (sublist.subset h₁)

theorem eval_ff_of_superlist_eval_ff {τ : assignment V} {c₁ c₂ : clause V} :
  c₁ <+ c₂ → clause.eval τ c₂ = ff → clause.eval τ c₁ = ff :=
assume h₁, eval_ff_of_superset_eval_ff (sublist.subset h₁)

theorem eval_tt_cons_of_eval_tt {τ : assignment V} {c : clause V} (l : literal V) :
  clause.eval τ c = tt → clause.eval τ (l :: c) = tt :=
assume h, eval_tt_of_sublist_eval_tt (sublist_cons l c) h

theorem eval_ff_of_eval_ff_cons {τ : assignment V} {c : clause V} {l : literal V} :
  clause.eval τ (l :: c) = ff → clause.eval τ c = ff :=
assume h, eval_ff_of_superlist_eval_ff (sublist_cons l c) h

end eval

/-! ### Counting -/
section counting

variables (τ : assignment V) (l : literal V) (c c₁ c₂ : clause V)

protected def count_tt : nat := c.countp (literal.is_true τ)
protected def count_ff : nat := c.countp (literal.is_false τ)

def count_pos (c : clause V) : nat := c.countp literal.is_pos
def count_neg (c : clause V) : nat := c.countp literal.is_neg

@[simp] lemma count_tt_nil : clause.count_tt τ [] = 0 := rfl
@[simp] lemma count_ff_nil : clause.count_ff τ [] = 0 := rfl
@[simp] lemma count_pos_nil : count_pos ([] : clause V) = 0 := rfl
@[simp] lemma count_neg_nil : count_neg ([] : clause V) = 0 := rfl

@[simp] theorem count_tt_singleton : clause.count_tt τ [l] = cond (l.eval τ) 1 0 :=
by cases h : (l.eval τ); simp [h, clause.count_tt, literal.is_true]

@[simp] theorem count_ff_singleton : clause.count_ff τ [l] = cond (l.eval τ) 0 1 :=
by cases h : (l.eval τ); simp [h, clause.count_ff, literal.is_false]

@[simp] theorem count_pos_singleton : count_pos [l] = cond l.is_pos 1 0 :=
by cases l; simp [count_pos, literal.is_pos]

@[simp] theorem count_neg_singleton : count_neg [l] = cond l.is_neg 1 0 :=
by cases l; simp [count_neg, literal.is_neg]

@[simp] theorem count_tt_cons : clause.count_tt τ (l :: c) = cond (l.eval τ) (1 + c.count_tt τ) (c.count_tt τ) :=
by cases h : (l.eval τ); simp [h, literal.is_true, clause.count_tt, add_comm]

@[simp] theorem count_ff_cons : clause.count_ff τ (l :: c) = cond (l.eval τ) (c.count_ff τ) (1 + c.count_ff τ) :=
by cases h : (l.eval τ); simp [h, literal.is_false, clause.count_ff, add_comm]

@[simp] theorem count_pos_cons : count_pos (l :: c) = cond l.is_pos (1 + c.count_pos) c.count_pos :=
by cases l; simp [count_pos, literal.is_pos, add_comm]

@[simp] theorem count_neg_cons : count_neg (l :: c) = cond l.is_neg (1 + c.count_neg) c.count_neg :=
by cases l; simp [count_neg, literal.is_neg, add_comm]

theorem count_tt_append : clause.count_tt τ (c₁ ++ c₂) = clause.count_tt τ c₁ + clause.count_tt τ c₂ :=
begin
  induction c₁ with l ls ih,
  { simp only [count_tt_nil, zero_add, nil_append] },
  { cases h : (literal.eval τ l); simp [h, ih, add_assoc] }
end

theorem count_ff_append : clause.count_ff τ (c₁ ++ c₂) = clause.count_ff τ c₁ + clause.count_ff τ c₂ :=
begin
  induction c₁ with l ls ih,
  { simp only [count_ff_nil, zero_add, nil_append] },
  { cases h : (literal.eval τ l); { simp [h, ih, add_assoc] } }
end

theorem count_pos_append : clause.count_pos (c₁ ++ c₂) = clause.count_pos c₁ + clause.count_pos c₂ :=
begin
  induction c₁ with l ls ih,
  { simp only [nil_append, count_pos_nil, zero_add] },
  { cases l; simp [ih, literal.is_pos, add_assoc] }
end

theorem count_neg_append : clause.count_neg (c₁ ++ c₂) = clause.count_neg c₁ + clause.count_neg c₂ :=
begin
  induction c₁ with l ls ih,
  { simp only [nil_append, count_neg_nil, zero_add] },
  { cases l; { simp [ih, literal.is_neg, add_assoc] } }
end

theorem count_tt_le_length : c.count_tt τ ≤ c.length :=
by simp only [clause.count_tt, countp_eq_length_filter, length_filter]

theorem count_ff_le_length : c.count_ff τ ≤ c.length :=
by simp only [clause.count_ff, countp_eq_length_filter, length_filter]

theorem count_pos_le_length : c.count_pos ≤ c.length :=
by simp only [count_pos, countp_eq_length_filter, length_filter]

theorem count_neg_le_length : c.count_neg ≤ c.length :=
by simp only [count_neg, countp_eq_length_filter, length_filter]

theorem count_tt_plus_count_ff_eq_length (τ : assignment V) (c : clause V) :
  c.count_tt τ + c.count_ff τ = c.length :=
begin
  induction c with l ls ih,
  { simp },
  { cases h : (l.eval τ);
    simp [count_tt_cons, count_ff_cons, h, ← ih],
    { rw [add_assoc, add_comm (clause.count_ff τ ls) 1] },
    { rw [add_comm (clause.count_tt τ ls + clause.count_ff τ ls) 1, ← add_assoc] } }
end

theorem count_tt_eq_length_sub_count_ff : c.count_tt τ = c.length - c.count_ff τ :=
eq_tsub_of_add_eq (count_tt_plus_count_ff_eq_length τ c)

theorem count_ff_eq_length_sub_count_tt : c.count_ff τ = c.length - c.count_tt τ :=
eq_tsub_of_add_eq (add_comm (c.count_tt τ) (c.count_ff τ) ▸ count_tt_plus_count_ff_eq_length τ c)

theorem count_pos_plus_count_neg_eq_length : c.count_pos + c.count_neg = c.length :=
begin
  induction c with l ls ih,
  { simp },
  { cases l;
    simp [count_pos_cons, count_neg_cons, literal.is_pos, literal.is_neg, ← ih],
    { rw [add_comm (count_pos ls + count_neg ls) 1, ← add_assoc] },
    { rw [add_assoc, add_comm 1] } }
end

theorem count_pos_eq_length_sub_count_neg : c.count_pos = c.length - c.count_neg :=
eq_tsub_of_add_eq (count_pos_plus_count_neg_eq_length c)

theorem count_neg_eq_length_sub_count_pos : c.count_neg = c.length - c.count_pos :=
eq_tsub_of_add_eq (add_comm (c.count_pos) (c.count_neg) ▸ count_pos_plus_count_neg_eq_length c)

theorem count_tt_eq_zero_iff_eval_ff {τ : assignment V} {c : clause V} : 
  c.count_tt τ = 0 ↔ c.eval τ = ff :=
begin
  rw [clause.count_tt, countp_eq_zero, eval_ff_iff_forall_literal_eval_ff],
  split,
  { intros hc l hl,
    have := hc l hl,
    rw [literal.is_true, eq_ff_eq_not_eq_tt] at this,
    exact this },
  { intros hl a ha, simp [literal.is_true, hl a ha] }
end

theorem count_tt_gt_zero_iff_eval_tt {τ : assignment V} {c : clause V} :
  c.count_tt τ > 0 ↔ c.eval τ = tt :=
begin
  rw [clause.count_tt, eval_tt_iff_exists_literal_eval_tt],
  split,
  { intro hp,
    rcases (countp_pos _).mp hp with ⟨l, hl, he⟩,
    exact ⟨l, hl, he⟩ },
  { rintro ⟨l, hl, he⟩,
    exact (countp_pos _).mpr ⟨l, hl, he⟩ } 
end

end counting

/-! # falsify and truthify -/
section falsify

variables (τ : assignment V) (v : V) (l : list V) {c c₁ c₂ : clause V}

-- For any assignment and variables, there is a clause that evaluates to false
-- Simply map each variable in the list to the literal which evaluates to false
def falsify : clause V := l.map (λ v, cond (τ v) (Neg v) (Pos v))
def truthify : clause V := l.map (λ v, cond (τ v) (Pos v) (Neg v))

@[simp] lemma falsify_nil : falsify τ [] = [] := rfl
@[simp] lemma truthify_nil : truthify τ [] = [] := rfl

@[simp] lemma falsify_singleton : falsify τ [v] = cond (τ v) [Neg v] [Pos v] :=
by cases h : τ v; simp [h, falsify]

@[simp] lemma truthify_singleton : truthify τ [v] = cond (τ v) [Pos v] [Neg v] :=
by cases h : τ v; simp [h, truthify]

@[simp] theorem falsify_cons : falsify τ (v :: l) = cond (τ v) (Neg v :: falsify τ l) (Pos v :: falsify τ l) :=
by cases h : τ v; simp [falsify, map_cons, h]

@[simp] theorem truthify_cons : truthify τ (v :: l) = cond (τ v) (Pos v :: truthify τ l) (Neg v :: truthify τ l) :=
by cases h : τ v; simp [truthify, map_cons, h]

theorem falsify_eval_ff : clause.eval τ (falsify τ l) = ff :=
begin
  induction l with v vs ih,
  { rw [falsify_nil, eval_nil] },
  { cases h : (τ v); simp [h, eval_cons, literal.eval, ih] }
end

theorem truthify_eval_tt {l : list V} (hl : l ≠ []) : clause.eval τ (truthify τ l) = tt :=
begin
  induction l with v vs ih,
  { contradiction },
  { cases h : (τ v); simp [h, literal.eval, eval_cons] }
end

theorem flip_truthify_eq_falsify : map literal.flip (truthify τ l) = falsify τ l :=
begin
  induction l with v vs ih,
  { refl },
  { cases h : (τ v); simp [h, literal.eval, ih, literal.flip] }
end

theorem falsify_map_var_eq : map var (falsify τ l) = l :=
begin
  induction l with v vs ih,
  { refl },
  { cases h : (τ v);
    { simp only [falsify_cons, map_cons, h, var, true_and, eq_self_iff_true, cond],
      exact ih } }
end

theorem truthify_map_var_eq : map var (truthify τ l) = l :=
begin
  induction l with v vs ih,
  { refl },
  { cases h : (τ v);
    { simp only [truthify_cons, map_cons, h, var, true_and, eq_self_iff_true, cond],
      exact ih } }
end

theorem count_tt_falsify : clause.count_tt τ (falsify τ l) = 0 :=
count_tt_eq_zero_iff_eval_ff.mpr (falsify_eval_ff τ l)

lemma count_tt_truthify : clause.count_tt τ (truthify τ l) = length l :=
begin
  induction l with v vs ih,
  { refl },
  { cases h : τ v; simp [literal.eval, h, ih, add_comm] }
end

theorem count_tt_sublist : c₁ <+ c₂ → c₁.count_tt τ ≤ c₂.count_tt τ :=
assume h, by simp [clause.count_tt, sublist.countp_le (literal.is_true τ) h]

theorem count_ff_sublist : c₁ <+ c₂ → c₁.count_ff τ ≤ c₂.count_ff τ :=
assume h, by simp [clause.count_ff, sublist.countp_le (literal.is_false τ) h]

theorem count_pos_sublist : c₁ <+ c₂ → c₁.count_pos ≤ c₂.count_pos :=
assume h, by simp [count_pos, sublist.countp_le literal.is_pos h]

theorem count_neg_sublist : c₁ <+ c₂ → c₁.count_neg ≤ c₂.count_neg :=
assume h, by simp [count_neg, sublist.countp_le literal.is_neg h]

theorem pos_count_tt_iff_exists_tt {τ} : c.count_tt τ > 0 ↔ ∃ l, l ∈ c ∧ literal.is_true τ l :=
by simp [clause.count_tt, countp_pos]

theorem pos_count_ff_iff_exists_ff {τ} : c.count_ff τ > 0 ↔ ∃ l, l ∈ c ∧ literal.is_false τ l :=
by simp [clause.count_ff, countp_pos]

theorem pos_count_pos_iff_exists_pos : c.count_pos > 0 ↔ ∃ l, l ∈ c ∧ literal.is_pos l :=
by simp [count_pos, countp_pos]

theorem pos_count_neg_iff_exists_neg : c.count_neg > 0 ↔ ∃ l, l ∈ c ∧ literal.is_neg l :=
by simp [count_neg, countp_pos]

theorem count_tt_perm : c₁ ~ c₂ → c₁.count_tt τ = c₂.count_tt τ :=
begin
  intro hp,
  induction hp with x l₂ l₂' p IH  x y l₂  l₂ m₂ r₂ p₁ p₂ IH₁ IH₂,
  { refl },
  { simp [count_tt_cons, IH] },
  { simp [count_tt_cons], cases literal.eval τ x; cases literal.eval τ y; simp },
  { exact eq.trans IH₁ IH₂ }
end

end falsify

/-! # Flip counting -/
section flips

variables [decidable_eq V]

-- If two clauses have the same length, literals can be compared at each
-- position. If they are literal.flip's of each other, increment a counter
def count_flips : clause V → clause V → nat
| []         _        := 0
| _         []        := 0
| (l :: ls) (m :: ms) := ite (l.flip = m) 
                         (1 + count_flips ls ms) (count_flips ls ms)

@[simp] lemma count_flips_nil (c : clause V) : count_flips [] c = 0 :=
by cases c; refl

@[simp] theorem count_flips_cons (c₁ c₂ : clause V) (l₁ l₂ : literal V) :
  count_flips (l₁ :: c₁) (l₂ :: c₂) = ite (l₁.flip = l₂) 
    (1 + count_flips c₁ c₂) (count_flips c₁ c₂) :=
by by_cases l₁.flip = l₂; simp only [count_flips]

@[simp] theorem count_flips_self (c : clause V) : count_flips c c = 0 :=
begin
  induction c with l ls ih,
  { refl },
  { simp [count_flips, flip_ne, ih] }
end

theorem count_flips_comm (c₁ c₂ : clause V) : count_flips c₁ c₂ = count_flips c₂ c₁ :=
begin
  induction c₁ with l ls ih generalizing c₂,
  { cases c₂; simp [count_flips] },
  { cases c₂,
    { refl },
    { simp [count_flips, ih c₂_tl],
      by_cases h : (l.flip = c₂_hd),
      { simp [h, flip_eq_iff_eq_flip.mp h, flip_flip] },
      { simp [h, ne.symm (flip_ne_iff_ne_flip.mp h), flip_flip] } } }
end

theorem count_flips_pos_of_map_var_eq_of_neq {c₁ c₂ : clause V} :
  map var c₁ = map var c₂ → c₁ ≠ c₂ → count_flips c₁ c₂ > 0 :=
begin
  intros h hne,
  induction c₁ with l ls ih generalizing c₂,
  { exact absurd (eq_nil_of_map_eq_nil h.symm).symm hne },
  { rcases exists_map_cons_of_map_cons h.symm with ⟨x, xs, rfl, hxl, hxs⟩,
    unfold count_flips,
    rcases var_eq_iff_eq_or_flip_eq.mp hxl with rfl | rfl,
    { simp [ih (tail_eq_of_cons_eq h) (ne_tail_of_eq_head_of_ne hne rfl)] },
    { simp [flip_flip, nat.zero_lt_one_add] } }
end

theorem count_flips_falsify_eq_count_tt (τ : assignment V) (c : clause V) :
  count_flips c (falsify τ (map var c)) = clause.count_tt τ c :=
begin
  induction c with l ls ih,
  { simp },
  { cases l; { cases h : (τ l); { simp [var, h, literal.eval, literal.flip, ih] } } }
end

/-! ## Parity reasoning for evaluation -/

theorem eval_tt_of_map_var_eq_of_tt_ne_neg {τ : assignment V} {l : list V} {c : clause V} :
  map var c = l → clause.count_tt τ (map Pos l) ≠ count_neg c → c.eval τ = tt :=
begin
  induction l with v vs ih generalizing c,
  { rw map_eq_nil, rintro rfl, contradiction },
  { intros hc hne,
    rcases exists_cons_of_map_cons hc with ⟨l, ls, rfl, rfl, hls⟩,
    cases l,
    { cases h : τ l,
      { simp [literal.eval, var, literal.is_neg, h] at hne,
        exact eval_tt_cons_of_eval_tt _ (ih hls hne) },
      { simp [literal.eval, h] } },
    { cases h : τ l,
      { simp [literal.eval, h] },
      { simp [literal.eval, var, literal.is_neg, h] at hne,
        exact eval_tt_cons_of_eval_tt _ (ih hls hne) } } }
end

-- Corollary of the above wrt parity reasoning
theorem eval_tt_of_map_var_eq_of_ne_parity {τ : assignment V} {l : list V} {c : clause V} : 
  map var c = l → (clause.count_tt τ (map Pos l)).bodd ≠ (count_neg c).bodd → c.eval τ = tt :=
λ hc hcount, eval_tt_of_map_var_eq_of_tt_ne_neg hc (ne_of_apply_ne nat.bodd hcount)

-- Parity reasoning based on flips rather than negs
theorem eval_tt_of_ne_flips {τ : assignment V} {c₁ c₂ : clause V} :
  map var c₁ = map var c₂ → c₁.count_tt τ ≠ count_flips c₁ c₂ → c₂.eval τ = tt :=
begin
  induction c₁ with l ls ih generalizing c₂,
  { simp },
  { intros hc₂ hne,
    rcases exists_map_cons_of_map_cons hc₂.symm with ⟨m, ms, rfl, hm, hms⟩,
    cases m,
    { cases h : (τ m),
      { cases l;
        { unfold var at hm,
          simp [literal.eval, literal.flip, ← hm, h] at hne,
          exact eval_tt_cons_of_eval_tt _ (ih hms.symm hne) } },
      { simp only [eval_cons, literal.eval, hm, h, tt_bor] } },
    { cases h : (τ m),
      { simp only [eval_cons, literal.eval, hm, h, bnot, tt_bor] },
      { cases l;
        { unfold var at hm,
          simp [literal.eval, literal.flip, ← hm, h] at hne,
          exact eval_tt_cons_of_eval_tt _ (ih hms.symm hne) } } } }
end

end flips

/-! # vars -/
section vars

variables [decidable_eq V]

protected def vars : clause V → finset V
| []        := ∅
| (l :: ls) := {l.var} ∪ (vars ls) 
--| (l :: ls) := insert l.var (vars ls) -- Use insert instead?

@[simp] theorem vars_nil : clause.vars ([] : clause V) = ∅ := rfl

@[simp] theorem vars_singleton (l : literal V) : clause.vars [l] = {l.var} := rfl

theorem mem_vars_cons_self (l : literal V) (c : clause V) : l.var ∈ clause.vars (l :: c) :=
finset.mem_union_left _ (finset.mem_singleton_self l.var)

theorem mem_vars_cons_of_mem_vars {c : clause V} (l : literal V) {v : V} : 
  v ∈ c.vars → v ∈ clause.vars (l :: c) :=
assume h, finset.mem_union.mpr (or.inr h)

theorem vars_append (c₁ c₂ : clause V) : (c₁ ++ c₂).vars = c₁.vars ∪ c₂.vars :=
begin
  induction c₁ with l ls ih,
  { simp only [finset.empty_union, vars_nil, nil_append] },
  { simp only [cons_append, clause.vars, ih, finset.union_assoc], }
end

theorem vars_perm {c₁ c₂ : clause V} : c₁ ~ c₂ → c₁.vars = c₂.vars :=
begin
  intro hp,
  induction hp with x l₂ l₂' p IH  x y l₂  l₂ m₂ r₂ p₁ p₂ IH₁ IH₂,
  { refl },
  { unfold clause.vars, rw IH },
  { unfold clause.vars,
    rw [← finset.union_assoc, ← finset.union_assoc, finset.union_comm {x.var} {y.var}] },
  { exact eq.trans IH₁ IH₂ }
end

theorem mem_vars_of_mem {c : clause V} {l : literal V} : l ∈ c → l.var ∈ c.vars :=
begin
  induction c with d ds ih,
  { simp },
  { intro hl,
    rcases eq_or_ne_mem_of_mem hl with rfl | hm,
    { exact finset.mem_union.mpr (or.inl (finset.mem_singleton_self l.var)) },
    { exact finset.mem_union.mpr (or.inr (ih hm.2)) } }
end

theorem exists_mem_clause_of_mem_vars {c : clause V} {v : V} : 
  v ∈ c.vars → ∃ (l : literal V), l ∈ c ∧ l.var = v :=
begin
  induction c with l ls ih,
  { simp },
  { intro hmem, 
    by_cases h : (l.var = v),
    { use [l, mem_cons_self l ls, h] },
    { rcases finset.mem_union.mp hmem with h₁| h₂,
      { exact absurd (finset.mem_singleton.mp h₁).symm h },
      { rcases ih h₂ with ⟨m, hm, hv⟩, use [m, mem_cons_of_mem l hm, hv] } } }
end

theorem vars_subset_of_vars_cons (l : literal V) (c : clause V) : c.vars ⊆ clause.vars (l :: c) :=
finset.subset_union_right _ _

theorem vars_subset_of_subset {c₁ c₂ : clause V} : c₁ ⊆ c₂ → c₁.vars ⊆ c₂.vars :=
begin
  intros h v hv,
  rcases exists_mem_clause_of_mem_vars hv with ⟨l, hl, rfl⟩,
  exact mem_vars_of_mem (h hl)
end

section mem_vars_lemmas

variables {v : V} {c : clause V}

-- (map var c) and vars c are equivalent from a set perspective
theorem mem_vars_iff_mem_map_vars : v ∈ c.vars ↔ v ∈ map var c :=
begin
  split,
  { intro h,
    exact mem_map.mpr (exists_mem_clause_of_mem_vars h) },
  { intro h,
    rcases mem_map.mp h with ⟨l, hmem, hv⟩,
    exact hv ▸ mem_vars_of_mem hmem }
end

theorem not_mem_vars_iff_not_mem_map_vars : v ∉ map var c ↔ v ∉ c.vars :=
by simp [mem_vars_iff_mem_map_vars]

theorem mem_vars_iff_pos_or_neg_mem_clause : v ∈ c.vars ↔ (Pos v) ∈ c ∨ (Neg v) ∈ c :=
begin
  split,
  { intro h,
    rcases exists_mem_clause_of_mem_vars h with ⟨l, hmem, hv⟩,
    cases l; { rw ← hv, simp [var, hmem] } },
  { rintros (h | h); { exact mem_vars_of_mem h } }
end

theorem vars_append_subset_left (c₁ c₂ : clause V) : c₁.vars ⊆ (c₁ ++ c₂).vars :=
by { rw vars_append, exact finset.subset_union_left _ _ }

theorem vars_append_subset_right (c₁ c₂ : clause V) : c₂.vars ⊆ (c₁ ++ c₂).vars :=
by { rw vars_append, exact finset.subset_union_right _ _ }

theorem mem_vars_append_left {c₁ : clause V} (c₂) : v ∈ c₁.vars → v ∈ (c₁ ++ c₂).vars :=
assume h, vars_append_subset_left c₁ c₂ h

theorem mem_vars_append_right (c₁) {c₂ : clause V} : v ∈ c₂.vars → v ∈ (c₁ ++ c₂).vars :=
assume h, vars_append_subset_right c₁ c₂ h

theorem mem_left_or_right_of_mem_vars_append {c₁ c₂ : clause V} :
  v ∈ (c₁ ++ c₂).vars → (v ∈ c₁.vars) ∨ (v ∈ c₂.vars) :=
by { rw vars_append, exact finset.mem_union.mp }

theorem not_mem_vars_append_left {c₁ c₂ : clause V} : v ∉ (c₁ ++ c₂).vars → v ∉ c₁.vars :=
assume h, mt (mem_vars_append_left c₂) h

theorem not_mem_vars_append_right {c₁ c₂ : clause V} : v ∉ (c₁ ++ c₂).vars → v ∉ c₂.vars :=
assume h, mt (mem_vars_append_right c₁) h

theorem not_mem_vars_append_of_not_mem_of_not_mem {c₁ c₂ : clause V} :
  v ∉ c₁.vars → v ∉ c₂.vars → v ∉ (c₁ ++ c₂).vars :=
begin
  intros h₁ h₂ hcon,
  rcases mem_left_or_right_of_mem_vars_append hcon; { contradiction }
end

end mem_vars_lemmas

open assignment

variables {τ₁ τ₂ : assignment V} {c : clause V}

theorem eval_eq_of_eqod : (eqod τ₁ τ₂ c.vars) → c.eval τ₁ = c.eval τ₂ :=
begin
  intro h,
  cases hev : (c.eval τ₂),
  { rw eval_ff_iff_forall_literal_eval_ff at hev,
    apply eval_ff_iff_forall_literal_eval_ff.mpr,
    intros l hl,
    exact hev l hl ▸ eval_eq_of_eqod_of_var_mem h (mem_vars_of_mem hl) },
  { rcases eval_tt_iff_exists_literal_eval_tt.mp hev with ⟨l, hl, htt⟩,
    apply eval_tt_iff_exists_literal_eval_tt.mpr,
    use [l, hl],
    exact htt ▸ eval_eq_of_eqod_of_var_mem h (mem_vars_of_mem hl) }  
end

theorem count_tt_eq_of_eqod : (eqod τ₁ τ₂ c.vars) → c.count_tt τ₁ = c.count_tt τ₂ :=
begin
  induction c with l ls ih,
  { simp only [count_tt_nil, eqod_nil, vars_nil, forall_true_left] },
  { intro h,
    rw clause.vars at h,
    cases l;
    { rw literal.var at h,
      simp [literal.eval, eqod_union_left h l (finset.mem_singleton_self l), ih (eqod_union_right h)] } }
end

theorem count_tt_ite (c : clause V) : c.count_tt (assignment.ite c.vars τ₁ τ₂) = c.count_tt τ₁ :=
count_tt_eq_of_eqod (ite_eqod c.vars τ₁ τ₂)

end vars

end clause