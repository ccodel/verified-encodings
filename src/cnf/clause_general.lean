/-
This file contains the definition of a Boolean (disjunctive) clause (as in CNF).
This particular implementation has clauses as lists.

Authors: Cayden Codel, Jeremy Avigad, Marijn Heule
Carnegie Mellon Univeristy
-/

import cnf.literal_general
import cnf.assignment_general
import basic

import data.nat.basic
import init.data.nat.lemmas
import data.list.basic
import data.list.count
import data.list.nodup
import data.list.perm
import init.logic
import init.function

universe u

-- Represents the parametric type of the variable stored in the literal
variables {V : Type u} [decidable_eq V] [inhabited V]

/- (Disjunctive) clauses are lists of literals, joined by logical ORs. -/
def clause (V : Type u) := list (literal V)

namespace clause

open function
open literal
open list

/-! # Properties, borrowed from lists -/

instance : inhabited (clause V) := ⟨[default (literal V)]⟩

instance has_decidable_eq [s : decidable_eq (literal V)] : decidable_eq (clause V)
| []        []        := is_true rfl
| (a :: as) []        := is_false (λ h, list.no_confusion h)
| []        (b :: bs) := is_false (λ h, list.no_confusion h)
| (a :: as) (b :: bs) :=
  match s a b with
  | is_true hab  :=
    match has_decidable_eq as bs with
    | is_true habs  := is_true (eq.subst hab (eq.subst habs rfl))
    | is_false nabs := is_false (λ h, list.no_confusion h (λ _ habs, absurd habs nabs))
    end
  | is_false nab := is_false (λ h, list.no_confusion h (λ hab _, absurd hab nab))
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

/-! # Evaluation under assignment -/

/- The clause represents a disjunction, so we evaluate literals until tt is found -/
protected def eval (α : assignment V) (c : clause V) : bool :=
  c.foldr (λ l b, b || (literal.eval α l)) ff

-- Proving properties of the fold operation
lemma eval_op_left_comm (α : assignment V) : 
  left_commutative (λ (l : literal V) (b : bool), b || (literal.eval α l)) :=
assume l₁ l₂ b, by simp [bool.bor_comm, bool.bor_assoc]

@[simp] theorem eval_nil (α : assignment V) : clause.eval α [] = ff := rfl

@[simp] theorem eval_singleton (α : assignment V) (l : literal V) : 
  clause.eval α [l] = literal.eval α l :=
by simp [clause.eval]

theorem eval_cons (α : assignment V) (l : literal V) (c : clause V) : 
  clause.eval α (l :: c) = (literal.eval α l) || (clause.eval α c) :=
by simp [clause.eval, bool.bor_comm]

theorem ne_nil_of_eval_tt {α : assignment V} {c : clause V} : 
  clause.eval α c = tt → c ≠ [] :=
by { contrapose, simp, intro h, simp [h] }

lemma exists_literal_eval_tt_of_eval_tt {α : assignment V} {c : clause V} :
  clause.eval α c = tt → ∃ l ∈ c, literal.eval α l = tt :=
begin
  induction c with l ls ih,
  { contradiction },
  { intro h,
    simp [eval_cons] at h,
    cases h,
    { use [l, h] },
    { rcases ih h with ⟨l₂, hl, he⟩,
      use [l₂, mem_cons_of_mem l hl, he] } }
end

lemma eval_tt_of_exists_literal_eval_tt {α : assignment V} {c : clause V} :
  (∃ l ∈ c, literal.eval α l = tt) → clause.eval α c = tt :=
begin
  rintros ⟨l, hl, he⟩,
  induction c with d ds ih,
  { exact absurd hl (not_mem_nil _) },
  { rcases eq_or_ne_mem_of_mem hl with rfl | ⟨hne, hds⟩,
    { simp [eval_cons, he] },
    { simp [eval_cons, ih hds] } }
end

theorem eval_tt_iff_exists_literal_eval_tt {α : assignment V} {c : clause V} : 
  clause.eval α c = tt ↔ ∃ l ∈ c, literal.eval α l = tt :=
⟨exists_literal_eval_tt_of_eval_tt, eval_tt_of_exists_literal_eval_tt⟩

lemma forall_literal_eval_ff_of_mem_of_eval_ff {α : assignment V} {c : clause V} :
  clause.eval α c = ff → ∀ l ∈ c, literal.eval α l = ff :=
begin
  induction c with d ds ih,
  { simp },
  { simp [eval_cons],
    intros hl hds,
    exact and.intro hl (ih hds) }
end

lemma eval_ff_of_forall_literal_eval_ff {α : assignment V} {c : clause V} :
  (∀ l ∈ c, literal.eval α l = ff) → clause.eval α c = ff :=
begin
  induction c with l ls ih,
  { simp },
  { intro h,
    simp [eval_cons, h l (mem_cons_self l ls)],
    have : ∀ (m : literal V), m ∈ ls → literal.eval α m = ff,
    { intros m hm, exact h m (mem_cons_of_mem l hm) },
    exact ih this }
end

theorem eval_ff_iff_forall_literal_eval_ff {α : assignment V} {c : clause V} : 
  clause.eval α c = ff ↔ ∀ l ∈ c, literal.eval α l = ff :=
⟨forall_literal_eval_ff_of_mem_of_eval_ff, eval_ff_of_forall_literal_eval_ff⟩

theorem eval_tautology {c : clause V} {l : literal V} : 
  l ∈ c → l.flip ∈ c → ∀ (α : assignment V), clause.eval α c = tt :=
begin
  intros hl hlf α,
  apply eval_tt_iff_exists_literal_eval_tt.mpr,
  cases h : (literal.eval α l),
  { use [l.flip, hlf, eval_flip_of_eval h] },
  { use [l, hl, h] }
end

-- From a set POV, similarity becomes moot
theorem eval_sim (α : assignment V) {c₁ c₂ : clause V} : c₁ ~ c₂ → clause.eval α c₁ = clause.eval α c₂ :=
assume h, perm.foldr_eq (eval_op_left_comm α) h ff

-- More set-like properties for evaluation
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

theorem eval_tt_cons_of_eval_tt {α : assignment V} {c : clause V} (l : literal V) :
  clause.eval α c = tt → clause.eval α (l :: c) = tt :=
assume h, eval_tt_of_sublist_eval_tt (sublist_cons l c) h

theorem eval_ff_of_eval_ff_cons {α : assignment V} {c : clause V} {l : literal V} :
  clause.eval α (l :: c) = ff → clause.eval α c = ff :=
assume h, eval_ff_of_superlist_eval_ff (sublist_cons l c) h

/-! # Falsify and truthify -/

-- For any list of natural numbers and assignment, a false clause can be computed
def falsify : assignment V → list V → clause V
| α []        := []
| α (v :: vs) := if α v then Neg v :: falsify α vs else Pos v :: falsify α vs

-- And here's a companion function that might have fewer uses
-- NOTE: The empty case doesn't work, but the empty case is trivial anyways...
def truthify : assignment V → list V → clause V
| α []        := []
| α (v :: vs) := if α v then Pos v :: truthify α vs else Neg v :: truthify α vs

@[simp] lemma falsify_nil (α : assignment V) : falsify α [] = [] := rfl
@[simp] lemma truthify_nil (α : assignment V) : truthify α [] = [] := rfl

theorem falsify_eval_ff (α : assignment V) (l : list V) : clause.eval α (falsify α l) = ff :=
begin
  induction l with n ns ih,
  { simp },
  { cases h : (α n);
    { simp [falsify, h, eval_cons, literal.eval, ih] } }
end

theorem truthify_eval_tt (α : assignment V) {l : list V} (hl : l ≠ []) : 
  clause.eval α (truthify α l) = tt :=
begin
  induction l with n ms ih,
  { contradiction },
  { cases h : (α n);
    { simp [truthify, h, literal.eval, eval_cons] } }
end

-- Get rid of these next two?
theorem map_var_falsify_eq_list (α : assignment V) (l : list V) : map var (falsify α l) = l :=
begin
  induction l with n ns ih,
  { simp },
  { cases h : (α n);
    { simp [falsify, h, ih, var] } }
end

theorem map_var_truthify_eq_list (α : assignment V) (l : list V) : map var (truthify α l) = l :=
begin
  induction l with n ns ih,
  { simp },
  { cases h : (α n);
    { simp [truthify, h, ih, var] } }
end

theorem flip_truthify_eq_falsify (α : assignment V) (l : list V) : 
  map flip (truthify α l) = falsify α l :=
begin
  induction l with n ns ih,
  { simp },
  { cases h : (α n);
    { simp [h, literal.eval, ih, literal.flip, truthify, falsify] } }
end

/-! ### Counting -/

-- Why is the decidable pred needed?

/- Counts the number of literals that evaluate to true in the clause, under some assignment -/
def count_tt (α : assignment V) (c : clause V) : nat :=
  c.countp (is_true α)

/- Counts the number of literals that evaluate to false in the clause, under some assignment -/
def count_ff (α : assignment V) (c : clause V) : nat :=
  c.countp (is_false α)

/- Counts the number of positive literals in the clause -/
def count_pos (c : clause V) : nat :=
  c.countp is_pos

/- Counts the number of negative literals in the clause -/
def count_neg (c : clause V) : nat :=
  c.countp is_neg

@[simp] lemma count_tt_nil (α : assignment V) : 
  count_tt α [] = 0 := by dec_trivial

@[simp] lemma count_ff_nil (α : assignment V) : 
  count_ff α [] = 0 := by dec_trivial

@[simp] lemma count_pos_nil : 
  count_pos ([] : clause V) = 0 := by dec_trivial

@[simp] lemma count_neg_nil : 
  count_neg ([] : clause V) = 0 := by dec_trivial

@[simp] theorem count_tt_singleton (α : assignment V) (l : literal V) :
  count_tt α [l] = bool.to_nat (literal.eval α l) :=
by cases h : (literal.eval α l); { simp [h, count_tt, literal.is_true, bool.to_nat] }

@[simp] theorem count_ff_singleton (α : assignment V) (l : literal V) :
  count_ff α [l] = bool.to_nat (!literal.eval α l) :=
by cases h : (literal.eval α l); { simp [h, count_ff, literal.is_false, bool.to_nat] }

@[simp] theorem count_pos_singleton (l : literal V) :
  count_pos [l] = bool.to_nat (is_pos l) :=
by cases l; simp [count_pos, bool.to_nat, is_pos]

@[simp] theorem count_neg_singleton (l : literal V) :
  count_neg [l] = bool.to_nat (is_neg l) :=
by cases l; simp [count_neg, bool.to_nat, is_neg, is_pos]

theorem count_tt_cons (α : assignment V) (l : literal V) (c : clause V) :
  count_tt α (l :: c) = bool.to_nat (literal.eval α l) + count_tt α c :=
by cases h : (literal.eval α l); 
  { simp [h, bool.to_nat, literal.is_true, and_comm, add_comm, count_tt] }

theorem count_ff_cons (α : assignment V) (l : literal V) (c : clause V) :
  count_ff α (l :: c) = bool.to_nat (!literal.eval α l) + count_ff α c :=
by cases h : (literal.eval α l);
  { simp [h, bool.to_nat, literal.is_false, and_comm, add_comm, count_ff] }

theorem count_pos_cons (l : literal V) (c : clause V) :
  count_pos (l :: c) = bool.to_nat (is_pos l) + count_pos c :=
by cases l; { simp [count_pos, is_pos, bool.to_nat, add_comm] }

theorem count_neg_cons (l : literal V) (c : clause V) :
  count_neg (l :: c) = bool.to_nat (is_neg l) + count_neg c :=
by cases l; { simp [count_neg, is_neg, bool.to_nat, add_comm] }

-- All the above four functions are capped by the length of the clause
/-
theorem count_tt_le_length (α : assignment V) (c : list (literal V)) :
  count_tt α c ≤ length c :=
begin
  simp only [count_tt, countp_eq_length_filter, length_filter],
  
  exact length_filter,
end

theorem count_ff_le_length (α : assignment V) (c : clause V) : count_ff α c ≤ length c :=
begin
  induction c with l ls ih,
  { simp },
  { cases h : (literal.eval α l),
    { simp [count_ff_cons, h, bool.to_nat, ih, add_comm] },
    { simp [count_ff_cons, h, bool.to_nat, le_add_right ih] } }
end
--by simp only [count_ff, countp_eq_length_filter, length_filter]

theorem count_pos_le_length (c : clause V) : count_pos c ≤ length c :=
begin
  induction c with l ls ih,
  { simp },
  { cases l,
    { simp [count_pos_cons, is_pos, bool.to_nat, ih], 
      rw add_comm,
      exact add_le_add_right ih 1 },
    { simp [count_pos_cons, is_pos, bool.to_nat, le_add_right ih] } }
end
--by simp only [count_pos, countp_eq_length_filter, length_filter]

theorem count_neg_le_length (c : clause V) : count_neg c ≤ length c :=
begin
  induction c with l ls ih,
  { simp },
  { cases l,
    { simp [count_neg_cons, is_neg, bool.to_nat, le_add_right ih] },
    { simp [count_neg_cons, is_neg, bool.to_nat, ih], 
      rw add_comm,
      exact add_le_add_right ih 1 } }
end
--by simp only [count_neg, countp_eq_length_filter, length_filter]
-/

-- count_tt and count_ff are complements of each other
-- There's probably an astute nat lemma that cleans this up
/-
theorem count_tt_eq_length_sub_cont_ff (α : assignment V) (c : clause V) :
  count_tt α c = length c - count_ff α c :=
begin
  have : length c = length c, refl,
  rw length_eq_countp_add_countp (is_true α) at this,
  rw is_false_eq_neg_is_true α at this,
  induction c with l ls ih,
  { simp },
  { cases h : (literal.eval α l);
    simp [count_tt_cons, count_ff_cons, h, bool.to_nat, ih, add_comm 1, nat.add_sub_add_right],
    { rw add_comm ls.length 1,
      rw nat.add_sub_assoc (count_ff_le_length α ls) 1,
      rw add_comm } }
end

-- count_pos and count_neg are complements of each other
theorem count_pos_eq_length_sub_count_neg (c : clause V) :
  count_pos c = length c - count_neg c :=
begin
  induction c with l ls ih,
  { simp },
  { cases l;
    simp [ih, count_pos_cons, count_neg_cons, bool.to_nat, is_pos, is_neg],
    { rw add_comm ls.length 1,
      rw nat.add_sub_assoc (count_neg_le_length ls) 1 },
    { simp [add_comm 1] } }
end
-/

lemma count_tt_eq_zero_of_eval_ff {α : assignment V} {c : clause V} :
  clause.eval α c = ff → count_tt α c = 0 :=
begin
  induction c with l ls ih,
  { simp },
  { simp [eval_cons, count_tt_cons],
    intros hl hls,
    simp [hl, bool.to_nat, ih hls] }
end

lemma eval_ff_of_count_tt_eq_zero {α : assignment V} {c : clause V} :
  count_tt α c = 0 → clause.eval α c = ff :=
begin
  induction c with l ls ih,
  { simp },
  { simp [eval_cons, count_tt_cons, bool.to_nat, literal.eval],
    intros hl hls,
    simp [cond_ff_of_cond_eq_second_of_ne _ one_ne_zero hl, ih hls] }
end

theorem count_tt_eq_zero_iff_eval_ff {α : assignment V} {c : clause V} :
  clause.eval α c = ff ↔ count_tt α c = 0 :=
⟨count_tt_eq_zero_of_eval_ff, eval_ff_of_count_tt_eq_zero⟩

lemma count_tt_gt_zero_of_eval_tt {α : assignment V} {c : clause V} :
  clause.eval α c = tt → count_tt α c > 0 :=
begin
  induction c with l ls ih,
  { simp },
  { cases h : (literal.eval α l);
    simp [h, eval_cons, count_tt_cons, bool.to_nat],
    { intro hls, exact ih hls },
    { exact nat.zero_lt_one_add _ } }
end

lemma eval_tt_of_count_tt_gt_zero {α : assignment V} {c : clause V} :
  0 < count_tt α c → clause.eval α c = tt :=
begin
  induction c with l ls ih,
  { simp },
  { intro hc,
    cases h : (literal.eval α l),
    { simp [h, count_tt_cons, bool.to_nat, is_pos] at hc,
      simp [h, eval_cons, ih hc] },
    { apply eval_tt_of_exists_literal_eval_tt,
      use [l, mem_cons_self l ls, h] } }
end

theorem count_tt_gt_zero_iff_eval_tt {α : assignment V} {c : clause V} :
  clause.eval α c = tt ↔ count_tt α c > 0 :=
⟨count_tt_gt_zero_of_eval_tt, eval_tt_of_count_tt_gt_zero⟩

theorem count_tt_falsify (α : assignment V) (l : list V) :
  count_tt α (falsify α l) = 0 :=
count_tt_eq_zero_iff_eval_ff.mp (falsify_eval_ff α l)

lemma count_tt_truthify (α : assignment V) (c : clause V) :
  count_tt α (truthify α (map var c)) = length c :=
begin
  induction c with l ls ih,
  { simp },
  { cases l; { cases h : (α l);
    { simp [truthify, h, var, count_tt_cons, bool.to_nat, literal.eval, ih, add_comm] } } }
end

-- Falsify negates those literals that, if positive, are true
theorem count_tt_pos_eq_count_neg_falsify (α : assignment V) (l : list V) :
  count_tt α (map Pos l) = count_neg (falsify α l) :=
begin
  induction l with v vs ih,
  { simp },
  { cases h : (α v);
    { simp [count_tt_cons, h, falsify, count_neg_cons, literal.eval, is_neg, bool.to_nat, ih] } }
end

-- Sublist theorems (can have subset theorems too)
theorem count_pos_sublist {c₁ c₂ : clause V} : 
  c₁ <+ c₂ → count_pos c₁ ≤ count_pos c₂ :=
assume h, by simp [count_pos, sublist.countp_le is_pos h]

theorem count_neg_sublist {c₁ c₂ : clause V} :
  c₁ <+ c₂ → count_neg c₁ ≤ count_neg c₂ :=
assume h, by simp [count_neg, sublist.countp_le is_neg h]

theorem count_tt_sublist (α : assignment V) {c₁ c₂ : clause V} :
  c₁ <+ c₂ → count_tt α c₁ ≤ count_tt α c₂ :=
assume h, by simp [count_tt, sublist.countp_le (is_true α) h]

theorem count_ff_sublist (α : assignment V) {c₁ c₂ : clause V} :
  c₁ <+ c₂ → count_ff α c₁ ≤ count_ff α c₂ :=
assume h, by simp [count_ff, sublist.countp_le (is_false α) h]

theorem exists_pos_iff_pos_count_pos {c : clause V} :
  count_pos c > 0 ↔ ∃ l ∈ c, is_pos l :=
by simp [count_pos, countp_pos]

theorem exists_neg_iff_pos_count_neg {c : clause V} :
  count_neg c > 0 ↔ ∃ l ∈ c, is_neg l :=
by simp [count_neg, countp_pos]

theorem exists_tt_iff_pos_count_tt {α : assignment V} {c : clause V} :
  count_tt α c > 0 ↔ ∃ l ∈ c, is_true α l :=
by simp [count_tt, countp_pos]

theorem exists_ff_iff_pos_count_ff {α : assignment V} {c : clause V} :
  count_ff α c > 0 ↔ ∃ l ∈ c, is_false α l :=
by simp [count_ff, countp_pos]

/-! # Flip counting -/

-- Flip counting
-- Not good from a set perspective, as order must be maintained
def count_flips : clause V → clause V → nat
| []         _        := 0
| _         []        := 0
| (l :: ls) (m :: ms) := ite (l.flip = m) (1 + count_flips ls ms) (count_flips ls ms)

@[simp] lemma count_flips_nil (c₁ c₂ : clause V) : 
  c₁ = [] ∨ c₂ = [] → count_flips c₁ c₂ = 0 :=
begin
  intro h, rcases h with rfl | rfl, 
  { cases c₂; { simp [count_flips] } },
  { cases c₁; { simp [count_flips] } }
end

theorem count_flips_cons (c₁ c₂ : clause V) (l₁ l₂ : literal V) :
  count_flips (l₁ :: c₁) (l₂ :: c₂) = bool.to_nat (l₁.flip = l₂) + count_flips c₁ c₂ :=
by { by_cases l₁.flip = l₂; simp [count_flips, h, bool.to_nat] }

lemma count_flips_self (c : clause V) : count_flips c c = 0 :=
begin
  induction c with l ls ih,
  { simp },
  { simp [count_flips, flip_ne, ih] }
end

lemma count_flips_comm (c₁ : clause V) : 
  ∀ (c₂ : clause V), count_flips c₁ c₂ = count_flips c₂ c₁ :=
begin
  induction c₁ with l ls ih,
  { simp },
  { intro c₂, cases c₂,
    { simp [count_flips] },
    { simp [count_flips, ih c₂_tl],
      cases classical.em (l.flip = c₂_hd),
      { simp [h, (congr_arg literal.flip h).symm], rw flip_flip l, simp },
      { have : l.flip.flip ≠ c₂_hd.flip, from flip_injective.ne h,
        rw flip_flip at this,
        simp [h, (ne.symm this)] } } }
end

theorem count_flips_pos_of_neq_of_map_var_eq {c₁ : clause V} :
  ∀ {c₂ : clause V}, map var c₁ = map var c₂ → c₁ ≠ c₂ → count_flips c₁ c₂ > 0 :=
begin
  induction c₁ with l ls ih,
  { intros c₂ h,
    simp at h,
    simp [eq_nil_of_map_eq_nil h.symm] },
  { intros c₂ h hneq,
    rcases exists_map_cons_of_map_cons h.symm with ⟨x, xs, rfl, hxl, hxs⟩,
    by_cases heq : l = x,
    { simp [count_flips, ih hxs.symm (ne_tail_of_eq_head_of_ne hneq heq), heq, flip_ne] },
    { rcases eq_or_flip_eq_of_var_eq hxl.symm with rfl | hlf,
      { contradiction },
      { simp [count_flips, nat.zero_lt_one_add, hlf] } } }
end

theorem count_flips_falsify_eq_count_tt (α : assignment V) (c : clause V) :
  count_flips c (falsify α (map var c)) = count_tt α c :=
begin
  induction c with l ls ih,
  { simp },
  { cases l; { cases h : (α l);
    { simp [falsify, count_flips, h, var, literal.flip, count_tt_cons, bool.to_nat, literal.eval, ih] } } }
end

/-! ## Parity reasoning for evaluation -/

-- This can probably be vastly shortened with a restatement or the introduction with a few supporting lemmas
theorem eval_tt_of_neq_counts {α : assignment V} {l : list V} :
  ∀ {c : clause V}, map var c = l → count_tt α (map Pos l) ≠ count_neg c → clause.eval α c = tt :=
begin
  induction l with v vs ih,
  { simp },
  { cases vs,
    { intros c hc hne,
      rcases exists_of_map_singleton hc with ⟨l, rfl, hl⟩,
      cases l; simp [is_neg, bool.to_nat] at hne; simp only [var] at hl,
      { simp [hl, cond_tt_of_not_cond_eq_second_of_ne (literal.eval α (Pos v)) one_ne_zero hne] },
      { have := cond_ff_of_not_cond_eq_first_of_ne (literal.eval α (Pos v)) zero_ne_one hne,
        simp [literal.eval] at this,
        simp [this, literal.eval, hl] } },
    { intros c hc hcount,
      rcases exists_cons_of_map_cons hc with ⟨l, ls, rfl, hl, hls⟩,
      have ihred := ih hls,
      cases l; rw var at hl,
      { cases h : (α v),
        { rw [map_cons, count_tt_cons] at hcount,
          simp [count_neg_cons, literal.eval, h, is_neg, bool.to_nat, cond, zero_add] at hcount,
          exact eval_tt_cons_of_eval_tt (Pos l) (ihred hcount) },
        { simp [eval_cons, literal.eval, h, hl] } },
      { cases h : (α v),
        { simp [eval_cons, literal.eval, h, hl] },
        { rw [map_cons, count_tt_cons] at hcount,
          simp [count_neg_cons, literal.eval, h, is_neg, bool.to_nat, cond] at hcount,
          exact eval_tt_cons_of_eval_tt (Neg l) (ihred hcount) } } } }
end

-- Basically the same proof here - shorten the above one, shorten this one
-- Take complement of the ≠ statement with length c to get the premises of the above?
theorem eval_tt_of_neq_counts2 {α : assignment V} {ns : list V} :
  ∀ {c : clause V}, map var c = ns → count_ff α (map Pos ns) ≠ count_pos c → clause.eval α c = tt :=
begin
  induction ns with m ms ih,
  { simp },
  { cases ms;
    intros c hc hne,
    { rcases exists_of_map_singleton hc with ⟨l, rfl, hl⟩,
      cases l; simp [is_pos, bool.to_nat] at hne; simp only [var] at hl,
      { have := cond_tt_of_not_cond_eq_second_of_ne (literal.eval α (Pos m)) zero_ne_one hne,
        simp [literal.eval] at this,
        simp [hl, this, literal.eval] },
      { have := cond_ff_of_not_cond_eq_first_of_ne (literal.eval α (Pos m)) one_ne_zero hne,
        simp [literal.eval] at this,
        simp [this, literal.eval, hl] } },
    { rcases exists_cons_of_map_cons hc with ⟨l, ls, rfl, hl, hls⟩,
      have ihred := ih hls,
      cases l; rw var at hl,
      { cases h : (α m),
        { rw [map_cons, count_ff_cons] at hne,
          simp [count_pos_cons, literal.eval, h, is_pos, bool.to_nat, cond, bnot] at hne,
          exact eval_tt_cons_of_eval_tt (Pos l) (ihred hne) },
        { simp [eval_cons, literal.eval, h, hl] } },
      { cases h : (α m),
        { simp [eval_cons, literal.eval, h, hl] },
        { rw [map_cons, count_ff_cons] at hne,
          simp [count_pos_cons, literal.eval, h, is_pos, bool.to_nat, cond, bnot, zero_add] at hne,
          exact eval_tt_cons_of_eval_tt (Neg l) (ihred hne) } } } }
end

-- Corollary of the above wrt parity reasoning
theorem eval_tt_of_opposite_parity {α : assignment V} {ns : list V} {c : clause V} :
  map var c = ns → nat.bodd (count_tt α (map Pos ns)) ≠ nat.bodd (count_neg c) → clause.eval α c = tt :=
assume hc hcount, eval_tt_of_neq_counts hc (ne_of_apply_ne nat.bodd hcount)

-- Parity reasoning based on flips rather than negs
-- If a clause evaluates to false, then any clause that can be made by flipping a
-- variable in that clause will evaluate to true
-- Shorten without much cases? Develop new tactic for symmetric casework?
theorem eval_tt_of_neq_flips {α : assignment V} {c₁ : clause V} :
  ∀ (c₂ : clause V), map var c₁ = map var c₂ → count_tt α c₁ ≠ count_flips c₁ c₂ → clause.eval α c₂ = tt :=
begin
  induction c₁ with l ls ih,
  { simp },
  { cases ls;
    intros c₂ hc₂ hcount,
    { rcases exists_of_map_singleton hc₂.symm with ⟨n, rfl, hn⟩,
      cases h : (α l.var),
      { cases l;
        rw var at h; 
        { cases n; rw [var, var] at hn,
          { simp [h, bool.to_nat, literal.eval, count_flips, literal.flip, hn] at hcount,
            contradiction },
          { simp [literal.eval, h, hn] } } },
      { cases l;
        rw var at h;
        { cases n; rw [var, var] at hn,
          { simp [literal.eval, h, hn] },
          { simp [h, bool.to_nat, literal.eval, count_flips, literal.flip, hn] at hcount,
            contradiction } } } },
    { rcases exists_map_cons_of_map_cons hc₂.symm with ⟨m, ms, rfl, hm, hms⟩,
      have ihred := ih ms hms.symm,
      cases h : (literal.eval α m),
      { by_cases he : l = m; rw count_tt_cons at hcount,
        { simp [h, he, count_flips_cons, bool.to_nat] at hcount,
          exact eval_tt_cons_of_eval_tt m (ihred hcount) },
        { have := eval_flip_of_eval h,
          simp [h, flip_eq_of_ne_of_var_eq (ne.symm he) hm] at this,
          simp [h, flip_eq_of_ne_of_var_eq he hm.symm, 
            count_flips_cons, bool.to_nat, this] at hcount,
          exact eval_tt_cons_of_eval_tt m (ihred hcount) } },
      { simp [eval_cons, h] } } }
end

/-! # Clause variables -/

/- Consider changing the implementation to a (fin)set

    The motivation for this is twofold
      1. Hide the implementation of clause as a list. Accessing the variables of the clause
         via the below function makes it so that (map var c) doesn't produce the same
      2. Allow for the same in cnf, etc.
-/

protected def vars : clause V → list V
| []        := []
| (l :: ls) := if (l ∈ ls ∨ l.flip ∈ ls) then vars ls else l.var :: vars ls

@[simp] theorem vars_nil : clause.vars ([] : clause V) = [] := rfl

@[simp] theorem vars_singleton (l : literal V) : clause.vars [l] = [l.var] := 
by simp [clause.vars]

theorem mem_vars_cons_of_mem_vars {c : clause V} (l : literal V) : 
  ∀ {v : V}, v ∈ clause.vars c → v ∈ clause.vars (l :: c) :=
assume v hv, by { by_cases (l ∈ c ∨ l.flip ∈ c); simp [clause.vars, h, hv] }

-- This one can probably be cleaned up with a lemma
theorem mem_vars_of_mem_clause {c : clause V} : 
  ∀ {l : literal V}, l ∈ c → l.var ∈ clause.vars c :=
begin
  induction c with d ds ih,
  { simp },
  { intros l hl,
    rcases eq_or_ne_mem_of_mem hl with rfl | hm,
    { rcases classical.em (l ∈ ds ∨ l.flip ∈ ds) with ⟨hds | hfds⟩ | h,
      { simp [ih hds, clause.vars, hds], },
      { exact flip_var_eq l ▸ mem_vars_cons_of_mem_vars l (ih hfds) },
      { simp [h, clause.vars] } },
    { exact mem_vars_cons_of_mem_vars d (ih hm.2) } }
end

-- Seems a little lengthy in casework
theorem exists_mem_clause_of_mem_vars {c : clause V} {v : V} : 
  v ∈ clause.vars c → ∃ (l : literal V), l ∈ c ∧ l.var = v :=
begin
  induction c with l ls ih,
  { simp },
  { by_cases (l ∈ ls ∨ l.flip ∈ ls),
    { simp [h, clause.vars],
      intro hn,
      rcases ih hn with ⟨m, hm, hms⟩,
      use m, simp [hm, hms] },
    { simp [h, clause.vars],
      rintros (hn | hn),
      { use l, simp [hn] },
      { rcases ih hn with ⟨m, hm, hms⟩,
        use m, simp [hm, hms] } } }
end

theorem vars_subset_of_vars_cons (c : clause V) (l : literal V) :
  clause.vars c ⊆ clause.vars (l :: c) :=
by { by_cases (l ∈ c ∨ l.flip ∈ c); simp [clause.vars, h] }

-- Unsurprisingly, (map var c) and vars c are equivalent from a set perspective
theorem vars_subset_of_map_var : ∀ (c : clause V), clause.vars c ⊆ map var c
| []        := by simp
| (l :: ls) := assume v hv, mem_map.mpr (exists_mem_clause_of_mem_vars hv)

theorem map_var_subset_of_vars : ∀ (c : clause V), map var c ⊆ clause.vars c
| []        := by simp
| (l :: ls) := assume v hv, by 
  { rcases mem_map.mp hv with ⟨l, hl, hls⟩, exact hls ▸ mem_vars_of_mem_clause hl }

theorem mem_vars_iff_mem_map_vars {c : clause V} {v : V} :
  v ∈ map var c ↔ v ∈ clause.vars c :=
⟨λ h, map_var_subset_of_vars c h, λ h, vars_subset_of_map_var c h⟩

theorem not_mem_vars_iff_not_mem_map_vars {c : clause V} {v : V} :
  v ∉ map var c ↔ v ∉ clause.vars c :=
by simp [mem_vars_iff_mem_map_vars]

-- Premises can be curried, but and_imp is being troublesome
theorem pos_or_neg_mem_clause_of_mem_vars {c : clause V} {v : V} :
  v ∈ clause.vars c → (Pos v) ∈ c ∨ (Neg v) ∈ c :=
begin
  intro h,
  rcases exists_mem_clause_of_mem_vars h with ⟨l, hl, hls⟩,
  cases l; { unfold var at hls, rw ← hls, simp [hl] }
end

theorem mem_vars_of_pos_or_neg_mem_clause {c : clause V} {v : V} :
  ((Pos v) ∈ c ∨ (Neg v) ∈ c) → v ∈ clause.vars c :=
begin
  rintros (h | h);
  { exact mem_vars_of_mem_clause h }
end

theorem mem_vars_iff_pos_or_neg_mem_clause {c : clause V} {v : V} :
  v ∈ clause.vars c ↔ (Pos v) ∈ c ∨ (Neg v) ∈ c :=
⟨pos_or_neg_mem_clause_of_mem_vars, mem_vars_of_pos_or_neg_mem_clause⟩

-- version of the above for literals?

theorem not_mem_vars_of_pos_not_mem_neg_not_mem {c : clause V} {v : V} :
  (Pos v) ∉ c → (Neg v) ∉ c → v ∉ clause.vars c :=
begin
  intros hp hn hv,
  rcases pos_or_neg_mem_clause_of_mem_vars hv with (h | h),
  { exact hp h },
  { exact hn h }
end

theorem pos_and_neg_not_mem_of_not_mem_vars {c : clause V} {v : V} :
  v ∉ clause.vars c → (Pos v) ∉ c ∧ (Neg v) ∉ c :=
begin
  intro h,
  split,
  { intro hp,
    exact h (mem_vars_of_pos_or_neg_mem_clause (or.inl hp)) },
  { intro hn,
    exact h (mem_vars_of_pos_or_neg_mem_clause (or.inr hn)) }
end

theorem vars_nodup (c : clause V) : c.vars.nodup :=
begin
  induction c with l ls ih,
  { simp },
  { simp [clause.vars],
    rcases (classical.em (l ∈ ls ∨ l.flip ∈ ls)) with ⟨hls | hls⟩ | h,
    repeat { simp [hls, ih] },
    { simp [h, ih], 
      simp [not_or_distrib] at h,
      rcases h with ⟨h1, h2⟩,
      cases l; unfold var; unfold literal.flip at h2,
      { exact not_mem_vars_of_pos_not_mem_neg_not_mem h1 h2 },
      { exact not_mem_vars_of_pos_not_mem_neg_not_mem h2 h1 } } }
end

-- Can pick a var not in the clause with a bijective mapping to the naturals
-- Just pick the next largest one
theorem exists_not_mem_of_bijection {f : V → nat} (hf : bijective f) (l : list V) :
  ∃ (v : V), v ∉ l :=
begin
  cases l,
  { use [(arbitrary V), not_mem_nil _] },
  { have : foldr max 0 (map f (l_hd :: l_tl)) + 1 > foldr max 0 (map f (l_hd :: l_tl)),
      from lt_add_one _,
    rcases exists_not_mem_of_gt_max hf this with ⟨v, heq, hv⟩,
    use [v, hv] }
end

-- Corollary, just mapped back to a clause
theorem exists_not_mem_clause_of_bijection {f : V → nat} (hf : bijective f) (c : clause V) :
  ∃ (v : V), (Pos v) ∉ c ∧ (Neg v) ∉ c :=
begin
  rcases exists_not_mem_of_bijection hf (map var c) with ⟨v, hv⟩,
  use [v, pos_and_neg_not_mem_of_not_mem_vars 
    (not_mem_vars_iff_not_mem_map_vars.mp hv)]
end

theorem exists_not_mem_vars_of_bijection {f : V → nat} (hf : bijective f) (c : clause V) :
  ∃ (v : V), v ∉ (clause.vars c) :=
exists_not_mem_of_bijection hf (clause.vars c)

end clause

/-! # Equivalence on domain for clauses -/

namespace assignment

open assignment
open list
open literal
open clause

theorem eval_eq_of_equiv_on_clause {α₁ α₂ : assignment V} {c : clause V} :
  (α₁ ≡[map var c]≡ α₂) → clause.eval α₁ c = clause.eval α₂ c :=
begin
  intro heq,
  cases h : (clause.eval α₂ c),
  { rw eval_ff_iff_forall_literal_eval_ff at h,
    apply eval_ff_iff_forall_literal_eval_ff.mpr,
    intros l hl,
    exact h l hl ▸ eval_eq_of_mem_of_eqod heq (mem_map_of_mem var hl) },
  { rcases eval_tt_iff_exists_literal_eval_tt.mp h with ⟨l, hl, hlt⟩,
    apply eval_tt_iff_exists_literal_eval_tt.mpr,
    use [l, hl],
    exact hlt ▸ eval_eq_of_mem_of_eqod heq (mem_map_of_mem var hl) }
end

theorem eval_eq_of_equiv_on_clause2 {α₁ α₂ : assignment V} {c : clause V} :
  (α₁ ≡[clause.vars c]≡ α₂) → clause.eval α₁ c = clause.eval α₂ c :=
assume h, eval_eq_of_equiv_on_clause (eqod_subset_of_eqod (map_var_subset_of_vars c) h)

end assignment