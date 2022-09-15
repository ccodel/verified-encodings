/-
This file contains the definitions of formulas in conjunctive normal form.
CNF is implemented as a list of clauses (see clause.lean).
The variable type used in the formula is polymorphic.

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

universe u

-- Represents the parametric type of the variable stored in the literal
variables {V : Type*} [decidable_eq V] [inhabited V]

/- Conjunctive normal form is a list of clauses joined by logical ANDs -/
def cnf (V : Type*) := list (clause V)

-- Note that the above definition allows for duplication of clauses (and
-- permutations of clauses), whereas a set definition would not (assuming a
-- set definition of clauses as well). However, lists allow for computable 
-- functions to be defined on them, which is important for proving that
-- encoding methods, which are computable, are equisatisfiable

namespace cnf

open literal
open clause
open list
open function 
open finset

/-! # Instance properties -/

instance : inhabited (cnf V) := ⟨[arbitrary (clause V)]⟩
instance : has_mem (clause V) (cnf V) := ⟨list.mem⟩
instance : has_emptyc (cnf V) := ⟨list.nil⟩
instance : has_union (cnf V) := ⟨list.union⟩
instance : has_inter (cnf V) := ⟨list.inter⟩
instance : has_singleton (clause V) (cnf V) := ⟨λ c, [c]⟩ 
instance : has_insert (clause V) (cnf V) := ⟨list.insert⟩
instance : has_append (cnf V) := ⟨list.append⟩
instance : has_subset (cnf V) := ⟨list.subset⟩
instance [has_repr V] : has_repr (cnf V) := ⟨list.repr⟩

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

-- Note: The below implementation works as well as a countp/filter, too
/- The clauses of the CNF are joined by conjunctions, so for the evaluation
   of a formula to be true, all clauses within must evaluate to true -/
protected def eval (τ : assignment V) (f : cnf V) : bool :=
  f.foldr (λ c b, b && (clause.eval τ c)) tt

@[simp] theorem eval_nil {τ : assignment V} : cnf.eval τ [] = tt := rfl

@[simp] theorem eval_singleton {τ : assignment V} {c : clause V} : 
  cnf.eval τ [c] = clause.eval τ c :=
by simp only [cnf.eval, foldr, tt_band]

theorem eval_cons {τ : assignment V} {c : clause V} {f : cnf V} : 
  cnf.eval τ (c :: f) = (clause.eval τ c && cnf.eval τ f) :=
by simp only [cnf.eval, foldr, bool.band_comm]

theorem eval_ff_cons_of_eval_ff {τ : assignment V} {f : cnf V} (c : clause V) :
  cnf.eval τ f = ff → cnf.eval τ (c :: f) = ff :=
assume h, by rw [eval_cons, h, band_ff]

theorem eval_append (τ : assignment V) (f₁ f₂ : cnf V) : 
  cnf.eval τ (f₁ ++ f₂) = cnf.eval τ f₁ && cnf.eval τ f₂ :=
begin
  unfold cnf.eval,
  rw foldr_append,
  cases foldr (λ c b, b && clause.eval τ c) tt f₂,
  { rw [band_ff, foldr_band_ff] },
  { rw band_tt }
end

theorem eval_tt_iff_forall_clause_eval_tt {τ : assignment V} {f : cnf V} :
  cnf.eval τ f = tt ↔ ∀ c ∈ f, clause.eval τ c = tt :=
begin
  split,
  { induction f with c cs ih,
    { intros _ c hc, exact absurd hc (not_mem_nil _) },
    { simp [eval_cons],
      intros hc hcs,
      exact and.intro hc (ih hcs) } },
  { induction f with c cs ih,
    { rw eval_nil, tautology },
    { simp [eval_cons],
      intros hc hcs,
      exact and.intro hc (ih hcs) } }
end

theorem eval_ff_iff_exists_clause_eval_ff {τ : assignment V} {f : cnf V} :
  cnf.eval τ f = ff ↔ ∃ c ∈ f, clause.eval τ c = ff :=
begin
  split,
  { induction f with c cs ih,
    { rw eval_nil, contradiction },
    { simp [eval_cons],
      rintros (hc | hcs),
      { use [c, hc] },
      { rcases ih hcs with ⟨cl, hcl₁, hcl₂⟩,
        use [cl, or.inr hcl₁, hcl₂] } } },
  { induction f with c cs ih,
    { rintros ⟨cl, hcl, _⟩, exact absurd hcl (not_mem_nil _) },
    { rintros ⟨cl, hcl, heval⟩,
      rcases eq_or_mem_of_mem_cons hcl with rfl | h,
      { rw [eval_cons, heval, ff_band] },
      { exact eval_ff_cons_of_eval_ff c (ih ⟨cl, h, heval⟩) } } }
end

theorem ne_nil_of_eval_ff {τ : assignment V} {f : cnf V} :
  f.eval τ = ff → f ≠ [] :=
begin
  intro h,
  rcases eval_ff_iff_exists_clause_eval_ff.mp h with ⟨cl, hcl, _⟩,
  exact ne_nil_of_mem hcl
end

def satisfiable (f : cnf V) := ∃ τ, f.eval τ = tt

theorem satisfiable_of_eval_tt (f : cnf V) (τ : assignment V) :
  f.eval τ = tt → satisfiable f :=
assume h, exists.intro τ h

/-! ### Counting -/

/- Counts the number of clauses which evaluate to true under some assignment -/
protected def count_tt (τ : assignment V) (f : cnf V) : nat :=
  f.countp (λ c, clause.eval τ c = tt)

/- Counts the number of clauses which evaluate to false under some assignment -/
protected def count_ff (τ : assignment V) (f : cnf V) : nat :=
  f.countp (λ c, clause.eval τ c = ff)

@[simp] theorem count_tt_nil (τ : assignment V) : cnf.count_tt τ [] = 0 := rfl
@[simp] theorem count_ff_nil (τ : assignment V) : cnf.count_ff τ [] = 0 := rfl

/-! # vars -/

-- Extract the variables used in the clauses, as a set
protected def vars : cnf V → finset V
| []        := ∅
| (c :: cs) := (c.vars) ∪ (vars cs)

@[simp] theorem vars_nil : cnf.vars ([] : cnf V) = ∅ := rfl

@[simp] theorem vars_singleton (c : clause V) : cnf.vars [c] = clause.vars c :=
by { unfold cnf.vars, rw finset.union_empty }

theorem vars_append (f₁ f₂ : cnf V) : cnf.vars (f₁ ++ f₂) = f₁.vars ∪ f₂.vars :=
begin
  induction f₁ with c cs ih,
  { simp only [empty_union, vars_nil, nil_append] },
  { simp only [cnf.vars, cons_append c cs f₂, ih, finset.union_assoc] }
end

theorem mem_vars_cons_of_mem_vars {f : cnf V} {v : V} (c : clause V) :
  v ∈ f.vars → v ∈ cnf.vars (c :: f) :=
assume h, finset.mem_union.mpr (or.inr h)

theorem clause_vars_subset_of_vars_of_mem {f : cnf V} {c : clause V} :
  c ∈ f → (c.vars) ⊆ f.vars :=
begin
  induction f with cl cls ih,
  { intro h, exact absurd h (not_mem_nil _) },
  { intros hc v hv,
    rcases eq_or_mem_of_mem_cons hc with rfl | hc,
    { unfold cnf.vars,
      rw finset.mem_union,
      exact or.inl hv },
    { exact mem_vars_cons_of_mem_vars cl (ih hc hv) } }
end

theorem mem_vars_iff_exists_mem_clause_and_mem {f : cnf V} {v : V} :
  v ∈ f.vars ↔ ∃ (c : clause V), c ∈ f ∧ v ∈ c.vars :=
begin
  induction f with cl cls ih,
  { simp only [not_mem_empty, not_mem_nil, exists_false, vars_nil, false_and] },
  { split,
    { intro hv,
      by_cases h : (v ∈ cl.vars),
      { use [cl, and.intro (mem_cons_self _ _) h] },
      { rcases ih.mp (or.resolve_left (finset.mem_union.mp hv) h) with ⟨c, hc, hv⟩,
        use [c, and.intro (mem_cons_of_mem cl hc) hv] } },
    { rintros ⟨c, hc, hv⟩,
      rw cnf.vars,
      rcases eq_or_mem_of_mem_cons hc with (rfl | hc),
      { exact finset.mem_union_left _ hv },
      { apply finset.mem_union_right,
        exact ih.mpr ⟨c, hc, hv⟩ } } }
end

theorem vars_subset_of_subset {f₁ f₂ : cnf V} :
  f₁ ⊆ f₂ → (cnf.vars f₁) ⊆ (cnf.vars f₂) :=
begin
  intros h v hv,
  rcases cnf.mem_vars_iff_exists_mem_clause_and_mem.mp hv with ⟨c, hf, hvc⟩,
  exact clause_vars_subset_of_vars_of_mem (h hf) hvc
end

/-! # Equisatisfiability -/

def equisatisfiable (f₁ f₂ : cnf V) :=
  (∃ (τ₁ : assignment V), cnf.eval τ₁ f₁ = tt) ↔ 
   ∃ (τ₂ : assignment V), cnf.eval τ₂ f₂ = tt

--notation f₁ ` ≈ ` f₂ := equisatisfiable f₁ f₂

@[simp] theorem equisatisfiable_nil : equisatisfiable ([] : cnf V) [] :=
⟨λ h, h, λ h, h⟩

@[refl] theorem equisatisfiable.refl (f : cnf V) : equisatisfiable f f :=
⟨λ h, h, λ h, h⟩

@[symm] theorem equisatisfiable.symm (f₁ f₂ : cnf V) :
  equisatisfiable f₁ f₂ → equisatisfiable f₂ f₁ :=
assume h, ⟨h.2, h.1⟩

@[trans] theorem equisatisfiable.trans {f₁ f₂ f₃ : cnf V} :
  equisatisfiable f₁ f₂ → equisatisfiable f₂ f₃ → equisatisfiable f₁ f₃ :=
begin
  rintros ⟨hmp1, hmpr1⟩ ⟨hmp2, hmpr2⟩,
  split,
  { intro h, exact hmp2 (hmp1 h) },
  { intro h, exact hmpr1 (hmpr2 h) }
end

end cnf

/-! # Equivalence on domain theorems -/

namespace assignment

open literal
open clause
open cnf
open list

theorem eval_eq_cnf_of_eqod {τ₁ τ₂ : assignment V} {f : cnf V} :
  (eqod τ₁ τ₂ f.vars) → f.eval τ₁ = f.eval τ₂ :=
begin
  intro h,
  cases hev : (cnf.eval τ₂ f),
  { apply eval_ff_iff_exists_clause_eval_ff.mpr,
    rcases eval_ff_iff_exists_clause_eval_ff.mp hev with ⟨c, hc, hff⟩,
    use [c, hc],
    exact hff ▸ eval_eq_clause_of_eqod 
      (eqod_subset (clause_vars_subset_of_vars_of_mem hc) h) },
  { apply eval_tt_iff_forall_clause_eval_tt.mpr,
    intros c hc,
    have := eval_tt_iff_forall_clause_eval_tt.mp hev c hc,
    exact this ▸ eval_eq_clause_of_eqod
      (eqod_subset (clause_vars_subset_of_vars_of_mem hc) h) }
end

end assignment