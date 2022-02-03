/-
This file contains the definition of a Boolean (disjunctive) clause.
This particular implementation has clauses as lists, although a set definition
is sufficient as well.

Authors: Cayden Codel, Jeremy Avigad, Marijn Heule
Carnegie Mellon Univeristy
-/

import cnf.literal
import cnf.assignment
import basic

import data.list.basic

universe u

-- Represents the parametric type of the variable stored in the literal
variables {V : Type u} [decidable_eq V] [inhabited V]

/- Disjunctive clauses are lists of literals, joined by logical ORs. -/
def clause (V : Type u) := list (literal V)

-- Note that the above definition allows for duplication of literals, whereas
-- a set definition would not. Lists also allow for computable functions,
-- while Lean sets are noncomputable by default

namespace clause

open function
open literal
open list

/-! # Properties -/

-- Many of these properties follow directly from lists

instance : inhabited (clause V) := ⟨[arbitrary (literal V)]⟩

instance has_decidable_eq : decidable_eq (clause V)
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
instance : has_union (clause V) := ⟨list.union⟩
instance : has_inter (clause V) := ⟨list.inter⟩
instance : has_singleton (literal V) (clause V) := ⟨λ l, [l]⟩ 
instance : has_insert (literal V) (clause V) := ⟨list.insert⟩
instance : has_append (clause V) := ⟨list.append⟩
instance : has_subset (clause V) := ⟨list.subset⟩

instance (l : literal V) (c : clause V) : decidable (l ∈ c) :=
by apply_instance

/-! # eval -/

-- Note: protected b/c many constructs will have an evaluation def
/- To evaluate the clause, fold false along until a true evaluation is found -/
protected def eval (α : assignment V) (c : clause V) : bool :=
  c.foldr (λ l b, b || (l.eval α)) ff

-- Proving properties of the fold operation
lemma eval_op_left_comm (α : assignment V) : 
  left_commutative (λ (l : literal V) (b : bool), b || (l.eval α)) :=
assume l₁ l₂ b, by simp [bool.bor_comm, bool.bor_assoc]

@[simp] theorem eval_nil (α : assignment V) : clause.eval α [] = ff := rfl

@[simp] theorem eval_singleton (α : assignment V) (l : literal V) : 
  clause.eval α [l] = l.eval α :=
by simp only [clause.eval, foldr, ff_bor]

-- TODO make this, and other similarly-named theorems, protected?
theorem eval_cons (α : assignment V) (l : literal V) (c : clause V) : 
  clause.eval α (l :: c) = (literal.eval α l) || (clause.eval α c) :=
by simp only [clause.eval, foldr, bool.bor_comm]

theorem eval_append (α : assignment V) (c₁ c₂ : clause V) :
  clause.eval α (c₁ ++ c₂) = c₁.eval α || c₂.eval α :=
begin
  unfold clause.eval,
  rw foldr_append,
  cases foldr (λ l b, b || literal.eval α l) ff c₂,
  { rw bor_ff },
  { rw [bor_tt, foldr_bor_tt] }
end

theorem eval_tt_iff_exists_literal_eval_tt {α : assignment V} {c : clause V} : 
  clause.eval α c = tt ↔ ∃ l ∈ c, literal.eval α l = tt :=
begin
  split,
  { induction c with l ls ih,
    { contradiction },
    { simp [eval_cons],
      intro h, cases h,
      { use [l, h] },
      { rcases ih h with ⟨l₂, hl, he⟩,
        use [l₂, mem_cons_of_mem l hl, he] } } },
  { rintros ⟨l, hl, he⟩,
    induction c with d ds ih,
    { exact absurd hl (not_mem_nil _) },
    { rcases eq_or_ne_mem_of_mem hl with rfl | ⟨hne, hds⟩,
      { simp [eval_cons, he] },
      { simp [eval_cons, ih hds] } } }
end

theorem ne_nil_of_eval_tt {α : assignment V} {c : clause V} :
  c.eval α = tt → c ≠ [] :=
begin
  intro h,
  rcases eval_tt_iff_exists_literal_eval_tt.mp h with ⟨l, hmem, _⟩,
  exact ne_nil_of_mem hmem
end

theorem eval_ff_iff_forall_literal_eval_ff {α : assignment V} {c : clause V} : 
  clause.eval α c = ff ↔ ∀ l ∈ c, literal.eval α l = ff :=
begin
  split,
  { induction c with l ls ih,
    { intros _ l hl, exact absurd hl (not_mem_nil l) },
    { simp [eval_cons],
      intros hl hds,
      exact and.intro hl (ih hds) } },
  { induction c with l ls ih,
    { rw eval_nil, tautology },
    { intro h,
      simp [eval_cons, h l (mem_cons_self l ls)],
      have : ∀ (m : literal V), m ∈ ls → literal.eval α m = ff,
      { intros m hm, exact h m (mem_cons_of_mem l hm) },
      exact ih this } }
end

theorem eval_tautology {c : clause V} {l : literal V} : 
  l ∈ c → l.flip ∈ c → ∀ (α : assignment V), clause.eval α c = tt :=
begin
  intros hl hlf α,
  apply eval_tt_iff_exists_literal_eval_tt.mpr,
  cases h : (literal.eval α l),
  { use [l.flip, hlf, eval_flip_of_eval h] },
  { use [l, hl, h] }
end

-- Evaluation of subsets and sublists tie in to evaluation nicely

theorem eval_tt_of_subset_eval_tt {α : assignment V} {c₁ c₂ : clause V} :
  c₁ ⊆ c₂ → clause.eval α c₁ = tt → clause.eval α c₂ = tt :=
begin
  intros h₁ h₂,
  apply eval_tt_iff_exists_literal_eval_tt.mpr,
  rcases eval_tt_iff_exists_literal_eval_tt.mp h₂ with ⟨l, hl, he⟩,
  use [l, h₁ hl, he]
end

theorem eval_ff_of_superset_eval_ff {α : assignment V} {c₁ c₂ : clause V} :
  c₁ ⊆ c₂ → clause.eval α c₂ = ff → clause.eval α c₁ = ff :=
begin
  intros h₁ h₂,
  apply eval_ff_iff_forall_literal_eval_ff.mpr,
  intros l hl,
  rw eval_ff_iff_forall_literal_eval_ff at h₂,
  exact h₂ l (h₁ hl)
end

theorem eval_tt_of_sublist_eval_tt {α : assignment V} {c₁ c₂ : clause V} :
  c₁ <+ c₂ → clause.eval α c₁ = tt → clause.eval α c₂ = tt :=
assume h₁, eval_tt_of_subset_eval_tt (sublist.subset h₁)

theorem eval_ff_of_superlist_eval_ff {α : assignment V} {c₁ c₂ : clause V} :
  c₁ <+ c₂ → clause.eval α c₂ = ff → clause.eval α c₁ = ff :=
assume h₁, eval_ff_of_superset_eval_ff (sublist.subset h₁)

theorem eval_tt_cons_of_eval_tt 
  {α : assignment V} {c : clause V} (l : literal V) :
  clause.eval α c = tt → clause.eval α (l :: c) = tt :=
assume h, eval_tt_of_sublist_eval_tt (sublist_cons l c) h

theorem eval_ff_of_eval_ff_cons 
  {α : assignment V} {c : clause V} {l : literal V} :
  clause.eval α (l :: c) = ff → clause.eval α c = ff :=
assume h, eval_ff_of_superlist_eval_ff (sublist_cons l c) h

/-! ### Counting -/

/- Counts the number of literals that evaluate to true, under α -/
protected def count_tt (α : assignment V) (c : clause V) : nat :=
  c.countp (literal.is_true α)

/- Counts the number of literals that evaluate to false, under α -/
protected def count_ff (α : assignment V) (c : clause V) : nat :=
  c.countp (literal.is_false α)

/- Counts the number of positive literals in the clause -/
def count_pos (c : clause V) : nat :=
  c.countp literal.is_pos

/- Counts the number of negative literals in the clause -/
def count_neg (c : clause V) : nat :=
  c.countp literal.is_neg

@[simp] lemma count_tt_nil (α : assignment V) : clause.count_tt α [] = 0 := rfl
@[simp] lemma count_ff_nil (α : assignment V) : clause.count_ff α [] = 0 := rfl
@[simp] lemma count_pos_nil : count_pos ([] : clause V) = 0 := rfl
@[simp] lemma count_neg_nil : count_neg ([] : clause V) = 0 := rfl

@[simp] theorem count_tt_singleton (α : assignment V) (l : literal V) :
  clause.count_tt α [l] = cond (l.eval α) 1 0 :=
by cases h : (l.eval α); { simp [h, clause.count_tt, literal.is_true] }

@[simp] theorem count_ff_singleton (α : assignment V) (l : literal V) :
  clause.count_ff α [l] = cond (l.eval α) 0 1 :=
by cases h : (l.eval α); { simp [h, clause.count_ff, literal.is_false] }

@[simp] theorem count_pos_singleton (l : literal V) :
  count_pos [l] = cond l.is_pos 1 0 :=
by cases l; simp [count_pos, literal.is_pos]

@[simp] theorem count_neg_singleton (l : literal V) :
  count_neg [l] = cond l.is_neg 1 0 :=
by cases l; simp [count_neg, literal.is_neg]

theorem count_tt_cons (α : assignment V) (l : literal V) (c : clause V) :
  clause.count_tt α (l :: c) = cond (l.eval α) (1 + c.count_tt α) (c.count_tt α) :=
by cases h : (literal.eval α l); 
  { simp [h, literal.is_true, clause.count_tt, add_comm] }

theorem count_ff_cons (α : assignment V) (l : literal V) (c : clause V) :
  clause.count_ff α (l :: c) = cond (l.eval α) (c.count_ff α) (1 + c.count_ff α) :=
by cases h : (literal.eval α l);
  { simp [h, literal.is_false, clause.count_ff, add_comm] }

theorem count_pos_cons (l : literal V) (c : clause V) :
  count_pos (l :: c) = cond l.is_pos (1 + c.count_pos) c.count_pos :=
by cases l; { simp [count_pos, literal.is_pos, add_comm] }

theorem count_neg_cons (l : literal V) (c : clause V) :
  count_neg (l :: c) = cond l.is_neg (1 + c.count_neg) c.count_neg :=
by cases l; { simp [count_neg, literal.is_neg, add_comm] }

theorem count_tt_append (α : assignment V) (c₁ c₂ : clause V) :
  clause.count_tt α (c₁ ++ c₂) = clause.count_tt α c₁ + clause.count_tt α c₂ :=
begin
  induction c₁ with l ls ih,
  { simp only [count_tt_nil, zero_add, nil_append] },
  { cases h : (literal.eval α l);
    { simp [count_tt_cons, h, ih, add_assoc] } }
end

-- Can make analogous append theorems for each of the others

-- All the above four functions are capped by the length of the clause
theorem count_tt_le_length (α : assignment V) (c : clause V) :
  c.count_tt α ≤ c.length :=
by simp only [clause.count_tt, countp_eq_length_filter, length_filter]

theorem count_ff_le_length (α : assignment V) (c : clause V) : 
  c.count_ff α ≤ c.length :=
by simp only [clause.count_ff, countp_eq_length_filter, length_filter]

theorem count_pos_le_length (c : clause V) : c.count_pos ≤ c.length :=
by simp only [count_pos, countp_eq_length_filter, length_filter]

theorem count_neg_le_length (c : clause V) : c.count_neg ≤ c.length :=
by simp only [count_neg, countp_eq_length_filter, length_filter]

-- count_tt and count_ff are complements of each other
theorem count_tt_plus_count_ff_eq_length (α : assignment V) (c : clause V) :
  c.count_tt α + c.count_ff α = c.length :=
begin
  induction c with l ls ih,
  { simp },
  { cases h : (l.eval α);
    simp [count_tt_cons, count_ff_cons, h, ← ih],
    { rw add_assoc,
      rw add_comm (clause.count_ff α ls) 1 },
    { rw add_comm (clause.count_tt α ls + clause.count_ff α ls) 1,
      rw ← add_assoc } }
end

theorem count_tt_eq_length_sub_count_ff (α : assignment V) (c : clause V) :
  c.count_tt α = c.length - c.count_ff α :=
eq_tsub_of_add_eq (count_tt_plus_count_ff_eq_length α c)

theorem count_ff_eq_length_sub_count_tt (α : assignment V) (c : clause V) :
  c.count_ff α = c.length - c.count_tt α :=
begin
  have := count_tt_plus_count_ff_eq_length α c,
  rw add_comm at this,
  exact eq_tsub_of_add_eq this
end

-- count_pos and count_neg are complements of each other
theorem count_pos_plus_count_neg_eq_length (c : clause V) :
  c.count_pos + c.count_neg = c.length :=
begin
  induction c with l ls ih,
  { simp },
  { cases l;
    simp [count_pos_cons, count_neg_cons, literal.is_pos, literal.is_neg, ← ih],
    { rw add_comm (count_pos ls + count_neg ls) 1,
      rw ← add_assoc },
    { rw add_assoc,
      rw add_comm 1 } }
end

theorem count_pos_eq_length_sub_count_neg (c : clause V) :
  c.count_pos = c.length - c.count_neg :=
eq_tsub_of_add_eq (count_pos_plus_count_neg_eq_length c)

theorem count_neg_eq_length_sub_count_pos (c : clause V) :
  c.count_neg = c.length - c.count_pos :=
begin
  have := count_pos_plus_count_neg_eq_length c,
  rw add_comm at this,
  exact eq_tsub_of_add_eq this
end

-- Note: A good countp lemma may reduce the forward direction
theorem count_tt_eq_zero_iff_eval_ff {α : assignment V} {c : clause V} :
  c.eval α = ff ↔ c.count_tt α = 0 :=
begin
  split,
  { induction c with l ls ih,
    { simp },
    { simp [eval_cons, count_tt_cons],
      intros hl hls,
      simp [hl, ih hls] } },
  { induction c with l ls ih,
    { simp },
    { simp [eval_cons, count_tt_cons],
      have : 1 + clause.count_tt α ls ≠ 0,
      { rw add_comm,
        rw ← nat.succ_eq_add_one,
        exact nat.succ_ne_zero _ },
      intro h,
      have := ff_of_ne_first_of_cond_eq this h,
      simp [this] at h,
      exact and.intro this (ih h) } }
end

theorem count_tt_eval_tt_iff_gt_zero {α : assignment V} {c : clause V} :
  c.eval α = tt ↔ clause.count_tt α c > 0 :=
begin
  split,
  { intro h,
    apply (countp_pos _).mpr,
    use eval_tt_iff_exists_literal_eval_tt.mp h },
  { intro h,
    apply eval_tt_iff_exists_literal_eval_tt.mpr,
    use (countp_pos _).mp h } 
end

/-! # falsify and truthify -/

-- For any assignment and variables, there is a false clause on those variables
-- Simply map each variable in the list to the literal which evaluates to false
def falsify (α : assignment V) (l : list V) : clause V :=
l.map (λ v, cond (α v) (Neg v) (Pos v))

-- For any assignment and variables, there is a true clause on those variables
-- Note: there is no such clause for the empty set of variables
def truthify (α : assignment V) (l : list V) : clause V :=
l.map (λ v, cond (α v) (Pos v) (Neg v))

@[simp] lemma falsify_nil (α : assignment V) : falsify α [] = [] := rfl
@[simp] lemma truthify_nil (α : assignment V) : truthify α [] = [] := rfl

@[simp] lemma falsify_singleton (α : assignment V) (v : V) :
  falsify α [v] = cond (α v) [Neg v] [Pos v] :=
by cases h : α v; { simp [h, falsify] }

@[simp] lemma truthify_singleton (α : assignment V) (v : V) :
  truthify α [v] = cond (α v) [Pos v] [Neg v] :=
by cases h : α v; { simp [h, truthify] }

theorem falsify_cons (α : assignment V) (v : V) (vs : list V) :
  falsify α (v :: vs) = cond (α v) (Neg v :: falsify α vs)
                                   (Pos v :: falsify α vs) :=
by cases h : α v; { simp [falsify, map_cons, h] }

theorem truthify_cons (α : assignment V) (v : V) (vs : list V) :
  truthify α (v :: vs) = cond (α v) (Pos v :: truthify α vs)
                                    (Neg v :: truthify α vs) :=
by cases h : α v; { simp [truthify, map_cons, h] }

theorem falsify_eval_ff (α : assignment V) (l : list V) :
  clause.eval α (falsify α l) = ff :=
begin
  induction l with v vs ih,
  { rw falsify_nil, rw eval_nil },
  { cases h : (α v);
    { simp [falsify_cons, h, eval_cons, literal.eval, ih] } }
end

theorem truthify_eval_tt (α : assignment V) {l : list V} (hl : l ≠ []) : 
  clause.eval α (truthify α l) = tt :=
begin
  induction l with v vs ih,
  { contradiction },
  { cases h : (α v);
    { simp [truthify_cons, h, literal.eval, eval_cons] } }
end

theorem flip_truthify_eq_falsify (α : assignment V) (l : list V) : 
  map literal.flip (truthify α l) = falsify α l :=
begin
  induction l with v vs ih,
  { simp },
  { cases h : (α v);
    { simp [h, literal.eval, ih, literal.flip, truthify_cons, falsify_cons] } }
end

-- If falsify/truthify become type (fin)set, these theorems aren't needed
theorem falsify_map_var_eq (α : assignment V) (l : list V) : 
  map var (falsify α l) = l :=
begin
  induction l with v vs ih,
  { simp only [falsify_nil, map_nil] },
  { cases h : (α v);
    { simp only [falsify_cons, map_cons, h, var, 
        true_and, eq_self_iff_true, cond],
      exact ih } }
end

theorem truthify_map_var_eq (α : assignment V) (l : list V) :
  map var (truthify α l) = l :=
begin
  induction l with v vs ih,
  { simp only [truthify_nil, map_nil] },
  { cases h : (α v);
    { simp only [truthify_cons, map_cons, h, var, 
        true_and, eq_self_iff_true, cond],
      exact ih } }
end

theorem count_tt_falsify (α : assignment V) (l : list V) :
  clause.count_tt α (falsify α l) = 0 :=
count_tt_eq_zero_iff_eval_ff.mp (falsify_eval_ff α l)

lemma count_tt_truthify (α : assignment V) (l : list V) :
  clause.count_tt α (truthify α l) = length l :=
begin
  induction l with v vs ih,
  { simp },
  { cases h : α v;
    { simp [truthify_cons, count_tt_cons, literal.eval, h, ih, add_comm] } }
end

-- Falsify negates those literals that, if positive, are true
theorem count_tt_pos_eq_count_neg_falsify (α : assignment V) (l : list V) :
  clause.count_tt α (map Pos l) = count_neg (falsify α l) :=
begin
  induction l with v vs ih,
  { simp },
  { cases h : (α v);
    { simp [map_cons, count_tt_cons, falsify_cons, count_neg_cons, 
        literal.eval, h, ih, literal.is_neg] } }
end

-- Sublist theorems (can have subset theorems too)
theorem count_pos_sublist {c₁ c₂ : clause V} : 
  c₁ <+ c₂ → c₁.count_pos ≤ c₂.count_pos :=
assume h, by simp [count_pos, sublist.countp_le literal.is_pos h]

theorem count_neg_sublist {c₁ c₂ : clause V} :
  c₁ <+ c₂ → c₁.count_neg ≤ c₂.count_neg :=
assume h, by simp [count_neg, sublist.countp_le literal.is_neg h]

theorem count_tt_sublist (α : assignment V) {c₁ c₂ : clause V} :
  c₁ <+ c₂ → c₁.count_tt α ≤ c₂.count_tt α :=
assume h, by simp [clause.count_tt, sublist.countp_le (literal.is_true α) h]

theorem count_ff_sublist (α : assignment V) {c₁ c₂ : clause V} :
  c₁ <+ c₂ → c₁.count_ff α ≤ c₂.count_ff α :=
assume h, by simp [clause.count_ff, sublist.countp_le (literal.is_false α) h]

theorem pos_count_pos_iff_exists_pos {c : clause V} :
  c.count_pos > 0 ↔ ∃ l ∈ c, literal.is_pos l :=
by simp [count_pos, countp_pos]

theorem pos_count_neg_iff_exists_neg {c : clause V} :
  c.count_neg > 0 ↔ ∃ l ∈ c, literal.is_neg l :=
by simp [count_neg, countp_pos]

theorem pos_count_tt_iff_exists_tt {α : assignment V} {c : clause V} :
  c.count_tt α > 0 ↔ ∃ l ∈ c, literal.is_true α l :=
by simp [clause.count_tt, countp_pos]

theorem pos_count_ff_iff_exists_ff {α : assignment V} {c : clause V} :
  c.count_ff α > 0 ↔ ∃ l ∈ c, literal.is_false α l :=
by simp [clause.count_ff, countp_pos]

/-! # Flip counting -/

-- If two clauses have the same length, literals can be compared at each
-- position. If they are literal.flip's of each other, increment a counter

-- Note: not good from a set perspective, as order must be maintained

def count_flips : clause V → clause V → nat
| []         _        := 0
| _         []        := 0
| (l :: ls) (m :: ms) := ite (l.flip = m) 
                         (1 + count_flips ls ms) (count_flips ls ms)

@[simp] lemma count_flips_nil (c₁ c₂ : clause V) : 
  c₁ = [] ∨ c₂ = [] → count_flips c₁ c₂ = 0 :=
begin
  intro h, rcases h with rfl | rfl, 
  { cases c₂; { simp [count_flips] } },
  { cases c₁; { simp [count_flips] } }
end

theorem count_flips_cons (c₁ c₂ : clause V) (l₁ l₂ : literal V) :
  count_flips (l₁ :: c₁) (l₂ :: c₂) = ite (l₁.flip = l₂) 
    (1 + count_flips c₁ c₂) (count_flips c₁ c₂) :=
by { by_cases l₁.flip = l₂; simp [count_flips, h] }

theorem count_flips_self (c : clause V) : count_flips c c = 0 :=
begin
  induction c with l ls ih,
  { refl },
  { simp [count_flips, flip_ne, ih] }
end

lemma count_flips_comm (c₁ c₂ : clause V) : 
  count_flips c₁ c₂ = count_flips c₂ c₁ :=
begin
  induction c₁ with l ls ih generalizing c₂,
  { simp },
  { cases c₂,
    { unfold count_flips },
    { simp [count_flips, ih c₂_tl],
      by_cases h : (l.flip = c₂_hd),
      { simp [h, flip_eq_iff_eq_flip.mp h, flip_flip] },
      { simp [h, ne.symm (flip_ne_iff_ne_flip.mp h), flip_flip] } } }
end

theorem count_flips_pos_of_map_var_eq_of_neq {c₁ c₂ : clause V} :
  map var c₁ = map var c₂ → c₁ ≠ c₂ → count_flips c₁ c₂ > 0 :=
begin
  induction c₁ with l ls ih generalizing c₂,
  { intros h₁ h₂,
    exact absurd (eq_nil_of_map_eq_nil h₁.symm).symm h₂ },
  { intros h hne,
    rcases exists_map_cons_of_map_cons h.symm with ⟨x, xs, rfl, hxl, hxs⟩,
    unfold count_flips,
    rcases var_eq_iff_eq_or_flip_eq.mp hxl with rfl | rfl,
    { simp [ih (tail_eq_of_cons_eq h) (ne_tail_of_eq_head_of_ne hne rfl)] },
    { simp [flip_flip, nat.zero_lt_one_add] } }
end

theorem count_flips_falsify_eq_count_tt (α : assignment V) (c : clause V) :
  count_flips c (falsify α (map var c)) = clause.count_tt α c :=
begin
  induction c with l ls ih,
  { simp },
  { cases l;
    { cases h : (α l);
      { simp [map_cons, falsify_cons, count_tt_cons, count_flips_cons, 
          literal.eval, h, var, literal.flip, ih] } } }
end

/-! ## Parity reasoning for evaluation -/

theorem eval_tt_of_tt_ne_neg_of_map_var_eq 
  {α : assignment V} {l : list V} {c : clause V} :
  map var c = l → clause.count_tt α (map Pos l) ≠ count_neg c → c.eval α = tt :=
begin
  induction l with v vs ih generalizing c,
  { rw map_eq_nil, rintro rfl, contradiction },
  { intros hc hne,
    rcases exists_cons_of_map_cons hc with ⟨l, ls, rfl, hl, hls⟩,
    cases l,
    { cases h : α v,
      { simp [map_cons, count_tt_cons, count_neg_cons, 
          literal.is_neg, literal.eval, h] at hne,
        exact eval_tt_cons_of_eval_tt _ (ih hls hne) },
      { unfold var at hl,
        simp [eval_cons, literal.eval, h, hl] } },
    { cases h : α v,
      { unfold var at hl,
        simp [eval_cons, literal.eval, h, hl] },
      { simp [map_cons, count_tt_cons, count_neg_cons, 
          literal.is_neg, literal.eval, h] at hne,
        exact eval_tt_cons_of_eval_tt _ (ih hls hne) } } }
end

-- Basically the same proof here as the one above
-- Take complement of count_ff, etc. to get above premises?
theorem eval_tt_of_ff_ne_pos_of_map_var_eq 
  {α : assignment V} {l : list V} {c : clause V} : map var c = l 
    → clause.count_ff α (map Pos l) ≠ count_pos c → c.eval α = tt :=
begin
  induction l with v vs ih generalizing c,
  { rw map_eq_nil, rintro rfl, contradiction },
  { intros hc hne,
    rcases exists_cons_of_map_cons hc with ⟨l, ls, rfl, hl, hls⟩,
    cases l,
    { cases h : α v,
      { simp [map_cons, count_ff_cons, count_pos_cons, 
          literal.is_pos, literal.eval, h] at hne,
        exact eval_tt_cons_of_eval_tt _ (ih hls hne) },
      { unfold var at hl,
        simp [eval_cons, literal.eval, h, hl] } },
    { cases h : α v,
      { unfold var at hl,
        simp [eval_cons, literal.eval, h, hl] },
      { simp [map_cons, count_ff_cons, count_pos_cons, 
          literal.is_pos, literal.eval, h] at hne,
        exact eval_tt_cons_of_eval_tt _ (ih hls hne) } } }
end

-- Corollary of the above wrt parity reasoning
theorem eval_tt_of_opposite_parity 
  {α : assignment V} {l : list V} {c : clause V} : map var c = l 
    → nat.bodd (clause.count_tt α (map Pos l)) ≠ nat.bodd (count_neg c) 
    → clause.eval α c = tt :=
assume hc hcount, 
  eval_tt_of_tt_ne_neg_of_map_var_eq hc (ne_of_apply_ne nat.bodd hcount)

-- Parity reasoning based on flips rather than negs
-- If a clause evaluates to false, then any clause that can be made by flipping a
-- variable in that clause will evaluate to true
theorem eval_tt_of_ne_flips {α : assignment V} {c₁ c₂ : clause V} :
  map var c₁ = map var c₂ → 
    clause.count_tt α c₁ ≠ count_flips c₁ c₂ → c₂.eval α = tt :=
begin
  induction c₁ with l ls ih generalizing c₂,
  { simp },
  { intros hc₂ hne,
    rcases exists_map_cons_of_map_cons hc₂.symm with ⟨m, ms, rfl, hm, hms⟩,
    cases m,
    { cases h : (α m),
      { cases l;
        { unfold var at hm,
          simp [count_tt_cons, count_flips_cons, 
            literal.eval, literal.flip, ← hm, h] at hne,
          exact eval_tt_cons_of_eval_tt _ (ih hms.symm hne) } },
      { simp only [eval_cons, literal.eval, hm, h, tt_bor] } },
    { cases h : (α m),
      { simp only [eval_cons, literal.eval, hm, h, bnot, tt_bor] },
      { cases l;
        { unfold var at hm,
          simp [count_tt_cons, count_flips_cons, 
            literal.eval, literal.flip, ← hm, h] at hne,
          exact eval_tt_cons_of_eval_tt _ (ih hms.symm hne) } } } }
end

/-! # vars -/

-- Extract the set of variables in the clause
-- As all properties are set-like properties, use a finset
protected def vars : clause V → finset V
| []        := ∅
| (l :: ls) := {l.var} ∪ (vars ls) -- Use insert instead?

@[simp] theorem vars_nil : clause.vars ([] : clause V) = ∅ := rfl

@[simp] theorem vars_singleton (l : literal V) : clause.vars [l] = {l.var} :=
by { unfold clause.vars, rw finset.union_empty }

theorem mem_vars_cons_of_mem_vars {c : clause V} (l : literal V) {v : V} : 
  v ∈ c.vars → v ∈ clause.vars (l :: c) :=
assume h, finset.mem_union.mpr (or.inr h)

theorem mem_vars_of_mem {c : clause V} {l : literal V} : 
  l ∈ c → l.var ∈ c.vars :=
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
      { rcases ih h₂ with ⟨m, hm, hv⟩,
        use [m, mem_cons_of_mem l hm, hv] } } }
end

theorem vars_subset_of_vars_cons (l : literal V) (c : clause V) :
  c.vars ⊆ clause.vars (l :: c) :=
finset.subset_union_right _ _

theorem vars_subset_of_subset {c₁ c₂ : clause V} :
  c₁ ⊆ c₂ → c₁.vars ⊆ c₂.vars :=
begin
  intros h v hv,
  rcases exists_mem_clause_of_mem_vars hv with ⟨l, hl, rfl⟩,
  exact mem_vars_of_mem (h hl)
end

-- (map var c) and vars c are equivalent from a set perspective
theorem mem_vars_iff_mem_map_vars {c : clause V} {v : V} :
  v ∈ c.vars ↔ v ∈ map var c :=
begin
  split,
  { intro h,
    exact mem_map.mpr (exists_mem_clause_of_mem_vars h) },
  { intro h,
    rcases mem_map.mp h with ⟨l, hmem, hv⟩,
    exact hv ▸ mem_vars_of_mem hmem }
end

theorem not_mem_vars_iff_not_mem_map_vars {c : clause V} {v : V} :
  v ∉ map var c ↔ v ∉ c.vars :=
by simp [mem_vars_iff_mem_map_vars]

theorem mem_vars_iff_pos_or_neg_mem_clause {c : clause V} {v : V} :
  v ∈ c.vars ↔ (Pos v) ∈ c ∨ (Neg v) ∈ c :=
begin
  split,
  { intro h,
    rcases exists_mem_clause_of_mem_vars h with ⟨l, hmem, hv⟩,
    cases l; { rw ← hv, simp [var, hmem] } },
  { rintros (h | h);
    { exact mem_vars_of_mem h } }
end

theorem vars_append_subset_left (c₁ c₂ : clause V) :
  clause.vars c₁ ⊆ clause.vars (c₁ ++ c₂) :=
begin
  intros v hv,
  rcases mem_vars_iff_pos_or_neg_mem_clause.mp hv with hv | hv;
  { have := mem_vars_of_mem (mem_append_left _ hv),
    assumption },
end

theorem vars_append_subset_right (c₁ c₂ : clause V) :
  clause.vars c₂ ⊆ clause.vars (c₁ ++ c₂) :=
begin
  intros v hv,
  rcases mem_vars_iff_pos_or_neg_mem_clause.mp hv with hv | hv;
  { have := mem_vars_of_mem (mem_append_right _ hv),
    assumption },
end

theorem mem_vars_append_left {v : V} {c₁ : clause V} (c₂ : clause V) :
  v ∈ clause.vars c₁ → v ∈ clause.vars (c₁ ++ c₂) :=
assume h, vars_append_subset_left c₁ c₂ h

theorem mem_vars_append_right {v : V} (c₁ : clause V) {c₂ : clause V} :
  v ∈ clause.vars c₂ → v ∈ clause.vars (c₁ ++ c₂) :=
assume h, vars_append_subset_right c₁ c₂ h

theorem mem_left_or_right_of_mem_vars_append {v : V} {c₁ c₂ : clause V} :
  v ∈ clause.vars (c₁ ++ c₂) → (v ∈ clause.vars c₁) ∨ (v ∈ clause.vars c₂) :=
begin
  intro h,
  rcases exists_mem_clause_of_mem_vars h with ⟨l, hl, rfl⟩,
  rcases mem_append.mp hl with hl | hl;
  { simp [mem_vars_of_mem hl] }
end

theorem not_mem_vars_append_left {v : V} {c₁ c₂ : clause V} :
  v ∉ clause.vars (c₁ ++ c₂) → v ∉ clause.vars c₁ :=
begin
  contrapose,
  simp,
  exact mem_vars_append_left c₂
end

theorem not_mem_vars_append_right {v : V} {c₁ c₂ : clause V} :
  v ∉ clause.vars (c₁ ++ c₂) → v ∉ clause.vars c₂ :=
begin
  contrapose,
  simp,
  exact mem_vars_append_right c₁
end

theorem not_mem_vars_append_of_not_mem_of_not_mem {v : V} {c₁ c₂ : clause V} :
  v ∉ clause.vars c₁ → v ∉ clause.vars c₂ → v ∉ clause.vars (c₁ ++ c₂) :=
begin
  intros h₁ h₂ hcon,
  rcases mem_left_or_right_of_mem_vars_append hcon with hv | hv;
  { contradiction }
end

end clause

/-! # eqod for clauses -/

namespace assignment

open clause

theorem eval_eq_clause_of_eqod {α₁ α₂ : assignment V} {c : clause V} :
  (α₁ ≡c.vars≡ α₂) → c.eval α₁ = c.eval α₂ :=
begin
  intro h,
  cases hev : (c.eval α₂),
  { rw eval_ff_iff_forall_literal_eval_ff at hev,
    apply eval_ff_iff_forall_literal_eval_ff.mpr,
    intros l hl,
    exact hev l hl ▸ eval_eq_of_eqod_of_var_mem h (mem_vars_of_mem hl) },
  { rcases eval_tt_iff_exists_literal_eval_tt.mp hev with ⟨l, hl, htt⟩,
    apply eval_tt_iff_exists_literal_eval_tt.mpr,
    use [l, hl],
    exact htt ▸ eval_eq_of_eqod_of_var_mem h (mem_vars_of_mem hl) }
end

-- Can replace α in count_tt if eqod
theorem count_tt_eq_of_eqod {α₁ α₂ : assignment V} {c : clause V} :
  (α₁ ≡c.vars≡ α₂) → clause.count_tt α₁ c = clause.count_tt α₂ c :=
begin
  induction c with l ls ih,
  { simp only [count_tt_nil, eqod_nil, vars_nil, forall_true_left] },
  { intro h,
    rw clause.vars at h,
    have ihred := ih (eqod_right_of_eqod_union h),
    cases l;
    { have := eqod_left_of_eqod_union h,
      rw literal.var at this,
      simp [count_tt_cons, literal.eval, 
        this l (finset.mem_singleton_self l), ihred] } }
end


end assignment