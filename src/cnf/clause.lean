/-
This file contains the definition of a Boolean (disjunctive) clause (as in CNF).
This particular implementation has clauses as lists.

Authors: Cayden Codel, Jeremy Avigad, Marijn Heule
Carnegie Mellon Univeristy
-/

import cnf.literal
import basic
import data.list.basic
import data.list.perm

/- (Disjunctive) clauses are lists of literals, joined by logical ORs. -/
def clause := list literal

namespace clause

open literal
open list

instance : inhabited clause := ⟨[default literal]⟩

instance has_decidable_eq [s : decidable_eq literal] : decidable_eq clause
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

instance : has_mem literal clause := ⟨list.mem⟩

instance : has_emptyc clause := ⟨list.nil⟩

instance : has_union clause := ⟨list.union⟩

instance : has_inter clause := ⟨list.inter⟩

instance : has_singleton literal clause := ⟨λ l, [l]⟩ 

instance : has_insert literal clause := ⟨list.insert⟩

instance : has_append clause := ⟨list.append⟩

/- The clause represents a disjunction, so we evaluate literals until tt is found -/
def eval (α : assignment) (c : clause) : bool :=
  c.foldr (λ l b, b || (l.eval α)) ff

@[simp] theorem eval_nil {α : assignment} : eval α [] = ff := rfl

@[simp] theorem eval_singleton {α : assignment} {l : literal} : eval α [l] = literal.eval α l := by simp [eval]

theorem eval_cons {α : assignment} {l : literal} {c : clause} : eval α (l :: c) = (literal.eval α l) || (eval α c) :=
  by simp [eval, bool.bor_comm]

theorem eval_erase_of_mem {α : assignment} {l : literal} {c : clause} (h : l ∈ c) : eval α c = (literal.eval α l) || (eval α (c.erase l)) :=
begin
  induction c with d ds ih,
  { exact absurd h (not_mem_nil _) },
  rcases classical.em (l = d) with rfl | hne,
  { simp [erase_cons_head, eval_cons] },
  { simp only [eval_cons, erase_cons_tail ds (ne.symm hne), ih (mem_of_ne_of_mem hne h), ← bool.bor_assoc, bool.bor_comm] }
end

theorem eval_erase_of_not_mem {α : assignment} {l : literal} {c : clause} (h : l ∉ c) : eval α c = eval α (c.erase l) :=
  by simp [erase_of_not_mem h]

/-! ### Similarity of clauses -/
-- Because clauses are literals joined by ORs, and OR is commutative, similar clauses evaluate identically

theorem eval_sim {α : assignment} {c₁ : clause} : ∀ (c₂ : clause), c₁ ~ c₂ → eval α c₁ = eval α c₂ :=
begin
  induction c₁ with l c ih; intros c₂ h,
  { simp [perm.nil_eq h] },
  { simp only [ih (c₂.erase l) (cons_perm_iff_perm_erase.mp h).2, 
      eval_cons, (eval_erase_of_mem ((perm.mem_iff h).mp (mem_cons_self l c))).symm] }
end


/-! ### Counting -/
/- Counts the number of literals that evaluate to true in the clause, under some assignment -/
def count_tt (α : assignment) (c : clause) : nat :=
  length $ c.filter (λ l, l.eval α = tt)

/- Counts the number of literals that evaluate to false in the clause, under some assignment -/
def count_ff (α : assignment) (c : clause) : nat :=
  length $ c.filter (λ l, l.eval α = ff)

/- Counts the number of positive literals in the clause -/
def count_pos (c : clause) : nat :=
  length $ c.filter (λ l, l.is_pos)

/- Counts the number of negative literals in the clause -/
def count_neg (c : clause) : nat :=
  length $ c.filter (λ l, literal.is_neg l)

end clause