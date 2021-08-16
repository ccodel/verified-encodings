/-

  This file contains the definition of a Boolean (disjunctive) clause (as in CNF).
  This particular implementation has clauses as finsets.

  Authors: Cayden Codel, Jeremy Avigad, Marijn Heule
  Carnegie Mellon Univeristy

-/

import data.finset
import cnf.literal
import basic

/- 
  (Disjunctive) clauses are finite sets of literals.
  The finite set represents the literals joined by logical ORs.
-/
def clause := finset literal

namespace clause

instance : has_mem literal clause := ⟨λ l c, l ∈ c.1⟩

-- TODO why is the mem_def and has_mem theorems/instance features required?
theorem mem_def {l : literal} {c : clause} : l ∈ c ↔ l ∈ c.1 := iff.rfl

instance : has_emptyc (clause) := ⟨finset.empty⟩

-- Define some equality
--instance has_decidable_eq : decidable_eq clause := sorry

instance : has_union (clause) := ⟨λ c₁ c₂, ⟨_, multiset.nodup_ndunion c₁.1 c₂.2⟩⟩

instance : has_singleton literal clause := ⟨λ l, ⟨{l}, list.nodup_singleton l⟩⟩ 

instance : has_insert literal clause := ⟨λ l c, ⟨_, multiset.nodup_ndinsert l c.2⟩⟩

theorem insert_def (l : literal) (c : clause) : insert l c = ⟨_, multiset.nodup_ndinsert l c.2⟩ := rfl

def erase (c : clause) (l : literal) : clause := ⟨_, multiset.nodup_erase_of_nodup l c.2⟩

/- The clause represents a disjunction, so we evaluate literals until tt is found -/
def eval (α : assignment) (c : clause) : bool :=
  cond (c.card > 0) (cond (∃ l ∈ c, literal.eval α l = tt) tt ff) ff

/- Counts the number of literals that evaluate to true in the clause, under some assignment -/
def count_tt (α : assignment) (c : clause) : nat :=
  finset.card $ c.filter (λ l, l.eval α = tt)

/- Counts the number of literals that evaluate to false in the clause, under some assignment -/
def count_ff (α : assignment) (c : clause) : nat :=
  finset.card $ c.filter (λ l, l.eval α = ff)

/- Counts the number of positive literals in the clause -/
/- TODO why can't I use a match statement? Requires decidable_pred... -/
def count_pos (c : clause) : nat :=
  --list.length $ c.filter (λ l, match l with | (literal.Pos _) := true | _ := false end)
  finset.card $ c.filter (λ l, literal.is_pos l = tt)

/- Counts the number of negative literals in the clause -/
def count_neg (c : clause) : nat :=
  finset.card $ c.filter (λ l, literal.is_neg l = tt)

/- Some useful statements for proofs of clauses -/
lemma empty_eval_ff {α : assignment} {c : clause} : c.card = 0 → eval α c = ff :=
begin
  -- This proof is very similar to the one for lists (change card to length)
  intro h,
  rw finset.card_eq_zero at h,
  rw h,
  unfold eval,
  simp,
end

-- TODO not sure whether to have this be forall or exists...
lemma single_eval_lit [inhabited literal] {α : assignment} {c : clause} : c.card = 1 → ∀ l ∈ c, eval α c = literal.eval α l :=
begin
  intros h l hin,
  rw finset.card_eq_one at h,
  cases h with a ha,
  rw ha at hin,
  have : l = a, from finset.mem_singleton.mp hin,
  rw this,
  rw ha,
  unfold eval,
  simp,
end

end clause