/-
This file contains the definitions of the conjunctive normal form.
Variables are general. 

Authors: Cayden Codel, Jeremy Avigad, Marijn Heule
Carnegie Mellon University
-/

import basic
import cnf.literal_general
import cnf.clause_general

import data.list.basic
import data.list.nodup
import data.list.perm
import init.data.nat
import data.nat.basic

universe u

-- Represents the parametric type of the variable stored in the literal
variables {V : Type u} [decidable_eq V] [inhabited V]

/- Conjunctive normal form is a list of clauses joined by logical ANDs -/
def cnf (V : Type u) := list (clause V)

namespace cnf

open literal
open clause
open list
open function 

/-! # Instance properties -/

instance : inhabited (cnf V) := ⟨[default (clause V)]⟩
instance : has_mem (clause V) (cnf V) := ⟨list.mem⟩
instance : has_emptyc (cnf V) := ⟨list.nil⟩
instance : has_union (cnf V) := ⟨list.union⟩
instance : has_inter (cnf V) := ⟨list.inter⟩
instance : has_singleton (clause V) (cnf V) := ⟨λ c, [c]⟩ 
instance : has_insert (clause V) (cnf V) := ⟨list.insert⟩
instance : has_append (cnf V) := ⟨list.append⟩
instance : has_subset (cnf V) := ⟨list.subset⟩

instance (c : clause V) (f : cnf V) : decidable (c ∈ f) :=
begin
  induction f with cl cls ih,
  { exact decidable.false },
  { cases ih,
    { by_cases h : c = cl,
      { rw h, exact decidable.is_true (mem_cons_self cl cls) },
      { exact decidable.is_false (not_mem_cons_of_ne_of_not_mem h ih) } },
    exact decidable.is_true (mem_cons_of_mem cl ih) }
end

/-! ### Evaluation under assignment -/

/- The clauses of the CNF are joined by conjunctions, so all must evaluate to true -/
protected def eval (α : assignment V) (f : cnf V) : bool :=
  f.foldr (λ c b, b && (clause.eval α c)) tt

@[simp] theorem eval_nil {α : assignment V} : cnf.eval α [] = tt := rfl

@[simp] theorem eval_singleton {α : assignment V} {c : clause V} : 
  cnf.eval α [c] = clause.eval α c :=
by simp [cnf.eval]

theorem eval_cons {α : assignment V} {c : clause V} {f : cnf V} : 
  cnf.eval α (c :: f) = (clause.eval α c && cnf.eval α f) :=
by simp [cnf.eval, bool.band_comm]

theorem ne_nil_of_eval_ff {α : assignment V} {f : cnf V} :
  cnf.eval α f = ff → f ≠ [] :=
by { contrapose, simp, intro h, simp [h] }

theorem eval_ff_cons_of_eval_ff {α : assignment V} {f : cnf V} (c : clause V) :
  cnf.eval α f = ff → cnf.eval α (c :: f) = ff :=
by { simp [cnf.eval], intro h, simp [h] }

theorem eval_append (α : assignment V) (f₁ f₂ : cnf V) : 
  cnf.eval α (f₁ ++ f₂) = cnf.eval α f₁ && cnf.eval α f₂ :=
by { induction f₁ with c cs ih, simp, simp [eval_cons, ih] }

lemma forall_clause_eval_tt_of_eval_tt {α : assignment V} {f : cnf V} : 
  cnf.eval α f = tt → ∀ c ∈ f, clause.eval α c = tt :=
begin
  induction f with c cs ih,
  { simp },
  { simp [eval_cons], 
    intros hc hcs,
    exact and.intro hc (ih hcs) }
end

lemma eval_tt_of_forall_clause_eval_tt {α : assignment V} {f : cnf V} :
  (∀ c ∈ f, clause.eval α c = tt) → cnf.eval α f = tt :=
begin
  induction f with c cs ih,
  { simp },
  { simp [eval_cons],
    intros hc he,
    simp [hc, ih he] }
end

theorem eval_tt_iff_forall_clause_eval_tt {α : assignment V} {f : cnf V} :
  cnf.eval α f = tt ↔ ∀ c ∈ f, clause.eval α c = tt :=
⟨forall_clause_eval_tt_of_eval_tt, eval_tt_of_forall_clause_eval_tt⟩

lemma exists_clause_eval_ff_of_eval_ff {α : assignment V} {f : cnf V} : 
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

lemma eval_ff_of_exists_clause_eval_ff {α : assignment V} {f : cnf V} :
  (∃ c ∈ f, clause.eval α c = ff) → cnf.eval α f = ff :=
begin
  induction f with c cs ih,
  { simp },
  { rintros ⟨cl, hcl, heval⟩,
    rcases eq_or_mem_of_mem_cons hcl with (rfl | h),
    { simp only [eval_cons, heval, ff_band] },
    { exact eval_ff_cons_of_eval_ff c (ih ⟨cl, h, heval⟩) } }
end

theorem eval_ff_iff_exists_clause_eval_ff {α : assignment V} {f : cnf V} :
  cnf.eval α f = ff ↔ ∃ c ∈ f, clause.eval α c = ff :=
⟨exists_clause_eval_ff_of_eval_ff, eval_ff_of_exists_clause_eval_ff⟩

/-! ### Counting -/

/- Counts the number of clauses which evaluate to true under some assignment -/
def count_tt (α : assignment V) (f : cnf V) : nat :=
  length $ f.filter (λ c, c.eval α = tt)

/- Counts the number of clauses which evaluate to false under some assignment -/
def count_ff (α : assignment V) (f : cnf V) : nat :=
  length $ f.filter (λ c, c.eval α = ff)

/-! ### Tseitin groundwork -/

-- A manual definition for vars using fold. Hard to prove things about
-- so the alternative definition is used
/-
def vars : cnf → list nat
| []        := []
| (c :: cs) := list.foldr (λ v s, if v ∈ s then s else v :: s) (vars cs) (clause.vars c)
-/

protected def vars : cnf V → list V
| []        := []
| (c :: cs) := (vars cs) ∪ (clause.vars c) -- I prefer the union the other way, but alas...

@[simp] theorem vars_nil : cnf.vars ([] : cnf V) = [] := rfl

@[simp] theorem vars_singleton (c : clause V) : cnf.vars [c] = clause.vars c :=
by simp [cnf.vars, var, nil_union]

theorem vars_append_subset_union (f₁ f₂ : cnf V) :
  cnf.vars (f₁ ++ f₂) ⊆ cnf.vars f₁ ∪ cnf.vars f₂ :=
begin
  sorry
end

theorem vars_union_subset_append (f₁ f₂ : cnf V) :
  cnf.vars f₁ ∪ cnf.vars f₂ ⊆ cnf.vars (f₁ ++ f₂) :=
begin
  sorry
end

theorem clause_vars_subset_of_mem {f : cnf V} {c : clause V} :
  c ∈ f → (clause.vars c) ⊆ cnf.vars f :=
begin
  intro h,
  induction f with d ds ih,
  { exact absurd h (not_mem_nil c) },
  { rcases eq_or_mem_of_mem_cons h with rfl | h2,
    { simp [cnf.vars],
      intros a ha,
      exact mem_union_right (cnf.vars ds) ha },
    { have ihred := ih h2,
      unfold cnf.vars,
      intros a ha,
      exact mem_union_left (ihred ha) (d.vars) } }
end

theorem mem_vars_of_mem_clause_of_mem {f : cnf V} {c : clause V} {v : V} :
  c ∈ f → v ∈ (clause.vars c) → v ∈ cnf.vars f :=
begin
  induction f with d ds ih,
  { simp },
  { intros hc hn,
    rcases eq_or_mem_of_mem_cons hc with rfl | hds,
    { simp [cnf.vars, hn] },
    { simp [cnf.vars, ih hds hn] } }
end

protected theorem exists_mem_clause_of_mem_vars {f : cnf V} {v : V} :
  v ∈ cnf.vars f → ∃ (c : clause V), c ∈ f ∧ v ∈ (clause.vars c) :=
begin
  induction f with c cs ih,
  { simp },
  { intro hn,
    simp [cnf.vars] at hn,
    rcases hn with hcs | hc,
    { rcases ih hcs with ⟨cl, hcl, hcls⟩,
      use cl,
      simp [mem_cons_of_mem c hcl, hcls] },
    { use c,
      simp [mem_cons_self c cs, hc] } }
end

theorem subset_vars_of_subset_cnf {f₁ f₂ : cnf V} :
  f₁ ⊆ f₂ → (cnf.vars f₁) ⊆ (cnf.vars f₂) :=
begin
  intros h n hn,
  rcases cnf.exists_mem_clause_of_mem_vars hn with ⟨c, hf, hnc⟩,
  exact mem_vars_of_mem_clause_of_mem (h hf) hnc
end

theorem exists_not_mem_vars_of_bijection {g : V → nat} (hg : bijective g) (f : cnf V) :
  ∃ (v : V), v ∉ cnf.vars f :=
begin
  cases f,
  { use [(arbitrary V), not_mem_nil _] },
  { have : foldr max 0 (map g (cnf.vars (f_hd :: f_tl))) + 1 > 
      foldr max 0 (map g (cnf.vars (f_hd :: f_tl))),
      from lt_add_one _,
    rcases exists_not_mem_of_gt_max hg this with ⟨v, heq, hv⟩,
    use [v, hv] }
end

-- Corollary of the above
theorem exists_not_mem_forall_clause_of_bijection 
  {g : V → nat} (hg : bijective g) (f : cnf V) :
  ∃ (v : V), ∀ (c : clause V), c ∈ f → v ∉ clause.vars c :=
begin
  rcases exists_not_mem_vars_of_bijection hg f with ⟨v, hv⟩,
  use v,
  intros c hc hvnot,
  have := clause_vars_subset_of_mem hc,
  exact hv (this hvnot)
end

/-! # Equisatisfiability -/

def equisatisfiable (f₁ f₂ : cnf V) :=
  (∃ (α₁ : assignment V), cnf.eval α₁ f₁ = tt) ↔ ∃ (α₂ : assignment V), cnf.eval α₂ f₂ = tt

notation f₁ ` ≈ ` f₂ := equisatisfiable f₁ f₂

@[simp] theorem equisatisfiable_nil : equisatisfiable ([] : cnf V) [] :=
by simp [equisatisfiable]

@[refl] theorem equisatisfiable.refl (f : cnf V) : f ≈ f :=
begin
  split;
  { rintros ⟨α, ha⟩,
    use [α, ha] }
end

@[symm] theorem equisatisfiable.symm (f₁ f₂ : cnf V) :
  f₁ ≈ f₂ → f₂ ≈ f₁ :=
begin
  unfold equisatisfiable,
  rintros ⟨hmp, hmpr⟩,
  exact ⟨hmpr, hmp⟩
end

@[trans] theorem equisatisfiable.trans {f₁ f₂ f₃ : cnf V} :
  f₁ ≈ f₂ → f₂ ≈ f₃ → f₁ ≈ f₃ :=
begin
  rintros ⟨hmp1, hmpr1⟩ ⟨hmp2, hmpr2⟩,
  split,
  { intro h, exact hmp2 (hmp1 h) },
  { intro h, exact hmpr1 (hmpr2 h) }
end

-- Can make this be an equivalence relation now

/-! # Equivalence -/

def equivalent (f₁ f₂ : cnf V) :=
  ∀ (α : assignment V), cnf.eval α f₁ = cnf.eval α f₂

end cnf

/-! # Equivalence on domain theorems -/

namespace assignment

open literal
open clause
open cnf
open list

theorem eval_eq_of_equiv_on_domain_vars {α₁ α₂ : assignment V} {f : cnf V} :
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