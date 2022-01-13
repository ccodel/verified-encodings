/-
This file contains the definitions of the conjunctive normal form. 

Authors: Cayden Codel, Jeremy Avigad, Marijn Heule
Carnegie Mellon University
-/

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

/-! # Instance properties -/

instance : inhabited cnf := ⟨[default clause]⟩
instance : has_mem clause cnf := ⟨list.mem⟩
instance : has_emptyc cnf := ⟨list.nil⟩
instance : has_union cnf := ⟨list.union⟩
instance : has_inter cnf := ⟨list.inter⟩
instance : has_singleton clause cnf := ⟨λ c, [c]⟩ 
instance : has_insert clause cnf := ⟨list.insert⟩
instance : has_append cnf := ⟨list.append⟩
instance : has_subset cnf := ⟨list.subset⟩

/-! ### Evaluation under assignment -/

/- The clauses of the CNF are joined by conjunctions, so all must evaluate to true -/
protected def eval (α : assignment) (f : cnf) : bool :=
  f.foldr (λ c b, b && (clause.eval α c)) tt

@[simp] theorem eval_nil {α : assignment} : cnf.eval α [] = tt := rfl

@[simp] theorem eval_singleton {α : assignment} {c : clause} : 
  cnf.eval α [c] = clause.eval α c :=
by simp [cnf.eval]

theorem eval_cons {α : assignment} {c : clause} {f : cnf} : 
  cnf.eval α (c :: f) = (clause.eval α c && cnf.eval α f) :=
by simp [cnf.eval, bool.band_comm]

theorem ne_nil_of_eval_ff {α : assignment} {f : cnf} :
  cnf.eval α f = ff → f ≠ [] :=
by { contrapose, simp, intro h, simp [h] }

theorem eval_ff_cons_of_eval_ff {α : assignment} {f : cnf} (c : clause) :
  cnf.eval α f = ff → cnf.eval α (c :: f) = ff :=
by { simp [cnf.eval], intro h, simp [h] }

theorem eval_append (α : assignment) (f₁ f₂ : cnf) : 
  cnf.eval α (f₁ ++ f₂) = cnf.eval α f₁ && cnf.eval α f₂ :=
by { induction f₁ with c cs ih, simp, simp [eval_cons, ih] }

lemma forall_clause_eval_tt_of_eval_tt {α : assignment} {f : cnf} : 
  cnf.eval α f = tt → ∀ c ∈ f, clause.eval α c = tt :=
begin
  induction f with c cs ih,
  { simp },
  { simp [eval_cons], 
    intros hc hcs,
    exact and.intro hc (ih hcs) }
end

lemma eval_tt_of_forall_clause_eval_tt {α : assignment} {f : cnf} :
  (∀ c ∈ f, clause.eval α c = tt) → cnf.eval α f = tt :=
begin
  induction f with c cs ih,
  { simp },
  { simp [eval_cons],
    intros hc he,
    simp [hc, ih he] }
end

theorem eval_tt_iff_forall_clause_eval_tt {α : assignment} {f : cnf} :
  cnf.eval α f = tt ↔ ∀ c ∈ f, clause.eval α c = tt :=
⟨forall_clause_eval_tt_of_eval_tt, eval_tt_of_forall_clause_eval_tt⟩

lemma exists_clause_eval_ff_of_eval_ff {α : assignment} {f : cnf} : 
  cnf.eval α f = ff → ∃ c ∈ f, clause.eval α c = ff :=
begin
  induction f with c cs ih,
  { simp },
  { simp [eval_cons], 
    rintros (hc | hcs),
    { use [c, hc] },
    { rcases ih hcs with ⟨c, hc1, hc2⟩,
      use c, simp [hc1, hc2] } },
end

lemma eval_ff_of_exists_clause_eval_ff {α : assignment} {f : cnf} :
  (∃ c ∈ f, clause.eval α c = ff) → cnf.eval α f = ff :=
begin
  induction f with c cs ih,
  { simp },
  { rintros ⟨cl, hcl, heval⟩,
    rcases eq_or_mem_of_mem_cons hcl with (rfl | h),
    { simp only [eval_cons, heval, ff_band] },
    { exact eval_ff_cons_of_eval_ff c (ih ⟨cl, h, heval⟩) } }
end

theorem eval_ff_iff_exists_clause_eval_ff {α : assignment} {f : cnf} :
  cnf.eval α f = ff ↔ ∃ c ∈ f, clause.eval α c = ff :=
⟨exists_clause_eval_ff_of_eval_ff, eval_ff_of_exists_clause_eval_ff⟩

/-! ### Counting -/

/- Counts the number of clauses which evaluate to true under some assignment -/
def count_tt (α : assignment) (f : cnf) : nat :=
  length $ f.filter (λ c, c.eval α = tt)

/- Counts the number of clauses which evaluate to false under some assignment -/
def count_ff (α : assignment) (f : cnf) : nat :=
  length $ f.filter (λ c, c.eval α = ff)

/-! ### Tseitin groundwork -/

-- A manual definition for vars using fold. Hard to prove things about
-- so the alternative definition is used
/-
def vars : cnf → list nat
| []        := []
| (c :: cs) := list.foldr (λ v s, if v ∈ s then s else v :: s) (vars cs) (clause.vars c)
-/

def vars : cnf → list nat
| []        := []
| (c :: cs) := (vars cs) ∪ (clause.vars c) -- I prefer the union the other way, but alas...

@[simp] theorem vars_nil : vars [] = [] := rfl

@[simp] theorem vars_singleton (c : clause) : vars [c] = clause.vars c :=
by simp [vars, var, nil_union]

theorem clause_vars_subset_of_mem {f : cnf} {c : clause} :
  c ∈ f → (clause.vars c) ⊆ vars f :=
begin
  intro h,
  induction f with d ds ih,
  { exact absurd h (not_mem_nil c) },
  { rcases eq_or_mem_of_mem_cons h with rfl | h2,
    { simp [vars],
      intros a ha,
      exact mem_union_right (vars ds) ha },
    { have ihred := ih h2,
      unfold vars,
      intros a ha,
      exact mem_union_left (ihred ha) (d.vars) } }
end

theorem mem_vars_of_mem_clause_of_mem {f : cnf} {c : clause} {n : nat} :
  c ∈ f → n ∈ (clause.vars c) → n ∈ vars f :=
begin
  induction f with d ds ih,
  { simp },
  { intros hc hn,
    rcases eq_or_mem_of_mem_cons hc with rfl | hds,
    { simp [vars, hn] },
    { simp [vars, ih hds hn] } }
end

protected theorem exists_mem_clause_of_mem_vars {f : cnf} {n : nat} :
  n ∈ vars f → ∃ (c : clause), c ∈ f ∧ n ∈ (clause.vars c) :=
begin
  induction f with c cs ih,
  { simp },
  { intro hn,
    simp [vars] at hn,
    rcases hn with hcs | hc,
    { rcases ih hcs with ⟨cl, hcl, hcls⟩,
      use cl,
      simp [mem_cons_of_mem c hcl, hcls] },
    { use c,
      simp [mem_cons_self c cs, hc] } }
end

theorem subset_vars_of_subset_cnf {f₁ f₂ : cnf} :
  f₁ ⊆ f₂ → (vars f₁) ⊆ (vars f₂) :=
begin
  intros h n hn,
  rcases cnf.exists_mem_clause_of_mem_vars hn with ⟨c, hf, hnc⟩,
  exact mem_vars_of_mem_clause_of_mem (h hf) hnc
end

theorem exists_not_mem_vars : ∀ (f : cnf), ∃ (n : nat), n ∉ (vars f)
| []        := by simp
| f := begin
  use (max_nat (vars f)) + 1,
  exact not_mem_of_gt_max_nat (lt_add_one (max_nat (vars f))),
end

end cnf

/-! # Equivalence on domain theorems -/

namespace assignment

open literal
open clause
open cnf
open list

theorem eval_eq_of_equiv_on_domain_vars {α₁ α₂ : assignment} {f : cnf} :
  (α₁ ≡[f.vars]≡ α₂) → cnf.eval α₁ f = cnf.eval α₂ f :=
begin
  intro h,
  cases he : (cnf.eval α₂ f),
  { apply eval_ff_iff_exists_clause_eval_ff.mpr,
    rcases eval_ff_iff_exists_clause_eval_ff.mp he with ⟨c, hc, hff⟩,
    use [c, hc],
    exact eval_eq_of_equiv_on_clause2 
      (eqod_subset_of_eqod (clause_vars_subset_of_mem hc) h).symm ▸ hff },
  { apply eval_tt_iff_forall_clause_eval_tt.mpr,
    intros c hc,
    exact (eval_eq_of_equiv_on_clause2
      (eqod_subset_of_eqod (clause_vars_subset_of_mem hc) h)).symm ▸
      (eval_tt_iff_forall_clause_eval_tt.mp he c hc) }
end

end assignment