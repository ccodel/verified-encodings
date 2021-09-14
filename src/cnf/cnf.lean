/-
This file contains the definitions of and basic operations on variables, literals,
clauses, and conjunctive normal form.

Authors: Cayden Codel, Jeremy Avigad, Marijn Heule
Carnegie Mellon University
-/

-- TODO: by_cases can often replace classical.em (a = b), etc.
-- TODO: Use variables to clean up theorem definitions, etc.

import basic
import cnf.literal
import cnf.clause

import data.list.basic
import data.list.nodup
import data.list.perm
import init.data.nat
import data.nat.basic

/- Conjunctive normal form is a list of clauses joined by logical ANDs -/
def cnf := list clause

namespace cnf

open literal
open clause
open list

/- Instance properties -/
instance : inhabited cnf := ⟨[default clause]⟩
instance : has_mem clause cnf := ⟨list.mem⟩
instance : has_emptyc cnf := ⟨list.nil⟩
instance : has_union cnf := ⟨list.union⟩
instance : has_inter cnf := ⟨list.inter⟩
instance : has_singleton clause cnf := ⟨λ c, [c]⟩ 
instance : has_insert clause cnf := ⟨list.insert⟩
instance : has_append cnf := ⟨list.append⟩

/-! # sim_erase -/
-- If we only care about evaluations, we can weaken the erase operation to removing similar clauses only
-- See clause.eval_sim for motivation

def sim_erase : cnf → clause → cnf
| []          c := []
| (cl :: cls) c := if cl ~ c then cls else cl :: sim_erase cls c

-- Technically, sim_erase "inherits" a lot of functionality from erase, as it is weaker
-- We reproduce only a few results here
@[simp] theorem sim_erase_nil {c : clause} : sim_erase [] c = [] := rfl

@[simp] theorem sim_erase_cons_head {c₁ c₂ : clause} {f : cnf} (h : c₁ ~ c₂) : sim_erase (c₁ :: f) c₂ = f :=
by simp [sim_erase, h]

theorem sim_erase_cons_tail {c₁ c₂ : clause} {f : cnf} (h : ¬(c₁ ~ c₂)) : sim_erase (c₁ :: f) c₂ = c₁ :: (sim_erase f c₂) :=
by simp [sim_erase, h]

theorem sim_erase_of_not_sim {c : clause} {f : cnf} (h : ∀ cl ∈ f, ¬(cl ~ c)) : sim_erase f c = f :=
begin
  induction f with cl cls ih,
  { simp [sim_erase_nil] },
  { simp [h cl (mem_cons_self cl cls), sim_erase], simp at h, simp [ih h.2] } -- TODO tighten up?
end

/-
by { induction f with cl cls ih, { exact sim_erase_nil },
  unfold sim_erase, have : ¬ cl ~ c, from h cl (mem_cons_self cl cls), simp [this], }
  -/

/-! ### Eval -/

/- The clauses of the CNF are joined by conjunctions, so all must evaluate to true -/
def eval (α : assignment) (f : cnf) : bool :=
  f.foldr (λ c, λ b, b && (c.eval α)) tt

@[simp] theorem eval_nil {α : assignment} : eval α [] = tt := rfl

@[simp] theorem eval_singleton {α : assignment} {c : clause} : eval α [c] = clause.eval α c := by simp [eval]

theorem eval_cons {α : assignment} {c : clause} {f : cnf} : eval α (c :: f) = (clause.eval α c && eval α f) :=
by simp [eval, bool.band_comm]

theorem eval_concat (α : assignment) (f₁ f₂ : cnf) : eval α (f₁ ++ f₂) = eval α f₁ && eval α f₂ :=
begin
  induction f₁ with c cs ih,
  { simp },
  { simp [eval_cons, ih] }
end

theorem eval_tt_iff_clauses_tt {α : assignment} {f : cnf} : eval α f = tt ↔ ∀ c ∈ f, clause.eval α c = tt :=
begin
  induction f with c cs ih,
  { simp }, split,
  { simp [eval_cons], 
    intros hc hcs,
    exact and.intro hc (ih.mp hcs) },
  { simp [eval_cons], 
    intros he ha,
    simp [he, ih.mpr ha] }
end

theorem eval_ff_iff_exists_clause_ff {α : assignment} {f : cnf} : eval α f = ff ↔ ∃ c ∈ f, clause.eval α c = ff :=
begin
  induction f with c cs ih,
  { simp }, split,
  { simp [eval_cons], 
    rintros (hc | hcs),
    { use c, simp [hc] },
    { rcases ih.mp hcs with ⟨c, hc1, hc2⟩,
      use c, simp [hc1, hc2] } },
  { simp [eval_cons],
    split,
    { intro hc, left, exact hc },
    { intros a ha haf, right,
      have : ∃ (cl : clause) (H : cl ∈ cs), clause.eval α cl = ff,
        { use a, simp [ha, haf] },
      exact ih.mpr this } }
end

/-! ### Counting -/

/- Counts the number of clauses which evaluate to true under some assignment -/
def count_tt (α : assignment) (f : cnf) : nat :=
  length $ f.filter (λ c, c.eval α = tt)

/- Counts the number of clauses which evaluate to false under some assignment -/
def count_ff (α : assignment) (f : cnf) : nat :=
  length $ f.filter (λ c, c.eval α = ff)

end cnf