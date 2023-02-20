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

-- Represents the parametric type of the variable stored in the literal
variables {V : Type*}

/- Conjunctive normal form is a list of clauses joined by logical ANDs -/
def cnf (V : Type*) := list (clause V)

-- Note that the above definition allows for duplication of clauses (and
-- permutations of clauses), whereas a set definition would not (assuming a
-- set definition of clauses as well). However, lists allow for computable 
-- functions to be defined on them.

namespace cnf

open literal
open clause
open list
open function 
open finset

/-! # Instance properties -/

instance [inhabited V] : inhabited (cnf V) := ⟨[arbitrary (clause V)]⟩
instance : has_mem (clause V) (cnf V) := ⟨list.mem⟩
instance : has_emptyc (cnf V) := ⟨list.nil⟩
instance [decidable_eq V] : has_union (cnf V) := ⟨list.union⟩
instance [decidable_eq V] : has_inter (cnf V) := ⟨list.inter⟩
instance : has_singleton (clause V) (cnf V) := ⟨λ c, [c]⟩ 
instance [decidable_eq V] : has_insert (clause V) (cnf V) := ⟨list.insert⟩
instance : has_append (cnf V) := ⟨list.append⟩
instance : has_subset (cnf V) := ⟨list.subset⟩
instance [has_repr V] : has_repr (cnf V) := ⟨list.repr⟩

instance [decidable_eq V] (c : clause V) (f : cnf V) : decidable (c ∈ f) :=
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
section eval

variables {τ : assignment V} {c : clause V} {f : cnf V}

protected def eval (τ : assignment V) (f : cnf V) : bool :=
  f.foldr (λ c b, b && (clause.eval τ c)) tt

@[simp] theorem eval_nil : cnf.eval τ [] = tt := rfl

@[simp] theorem eval_singleton : cnf.eval τ [c] = c.eval τ :=
by simp only [cnf.eval, foldr, tt_band]

@[simp] theorem eval_cons : cnf.eval τ (c :: f) = c.eval τ && f.eval τ :=
by simp only [cnf.eval, foldr, bool.band_comm]

theorem eval_ff_cons_of_eval_ff (c : clause V) : f.eval τ = ff → cnf.eval τ (c :: f) = ff :=
assume h, by rw [eval_cons, h, band_ff]

@[simp] theorem eval_append (τ : assignment V) (f₁ f₂ : cnf V) : 
  cnf.eval τ (f₁ ++ f₂) = f₁.eval τ && f₂.eval τ :=
begin
  unfold cnf.eval,
  rw foldr_append,
  cases foldr (λ c b, b && clause.eval τ c) tt f₂,
  { rw [band_ff, foldr_band_ff] },
  { rw band_tt }
end

theorem eval_tt_iff_forall_clause_eval_tt : f.eval τ = tt ↔ ∀ (c : clause V), c ∈ f → c.eval τ = tt :=
begin
  induction f with c cs ih,
  { simp only [eval_nil, eq_self_iff_true, not_mem_nil, is_empty.forall_iff, implies_true_iff] },
  { simp only [ih, eval_cons, band_eq_true_eq_eq_tt_and_eq_tt, mem_cons_iff, forall_eq_or_imp] }
end

theorem eval_ff_iff_exists_clause_eval_ff : f.eval τ = ff ↔ ∃ c, c ∈ f ∧ clause.eval τ c = ff :=
begin
  induction f with c cs ih,
  { simp only [eval_nil, not_mem_nil, false_and, exists_false] },
  { simp only [eval_cons, band_eq_false_eq_eq_ff_or_eq_ff, mem_cons_iff],
    split,
    { rintros (h | h),
      { use [c, or.inl rfl, h] },
      { rcases ih.mp h with ⟨c₂, hc, he⟩,
        use [c₂, mem_cons_of_mem c hc, he] } },
    { rintros ⟨c₂, (rfl | hc), he⟩,
      { exact or.inl he },
      { exact or.inr (ih.mpr ⟨c₂, hc, he⟩) } } }
end

end eval

def satisfiable (f : cnf V) := ∃ τ, f.eval τ = tt

theorem satisfiable_of_eval_tt (f : cnf V) (τ : assignment V) : f.eval τ = tt → satisfiable f :=
assume h, exists.intro τ h

/-! ### Counting -/
section counting

variables (τ : assignment V) (c : clause V) (f f₁ f₂ : cnf V)

protected def count_tt : nat := f.countp (λ c, clause.eval τ c = tt)
protected def count_ff : nat := f.countp (λ c, clause.eval τ c = ff)

@[simp] theorem count_tt_nil : cnf.count_tt τ [] = 0 := rfl
@[simp] theorem count_ff_nil : cnf.count_ff τ [] = 0 := rfl

@[simp] theorem count_tt_singleton : cnf.count_tt τ [c] = cond (c.eval τ) 1 0 :=
by cases h : (c.eval τ); simp [h, cnf.count_tt]

@[simp] theorem count_ff_singleton : cnf.count_ff τ [c] = cond (c.eval τ) 0 1 :=
by cases h : (c.eval τ); simp [h, cnf.count_ff]

@[simp] theorem count_tt_cons : cnf.count_tt τ (c :: f) = cond (c.eval τ) (1 + f.count_tt τ) (f.count_tt τ) :=
by cases h : (c.eval τ); simp [h, cnf.count_tt, add_comm]

@[simp] theorem count_ff_cons : cnf.count_ff τ (c :: f) = cond (c.eval τ) (f.count_ff τ) (1 + f.count_ff τ) :=
by cases h : (c.eval τ); simp [h, cnf.count_ff, add_comm]

theorem count_tt_append : cnf.count_tt τ (f₁ ++ f₂) = cnf.count_tt τ f₁ + cnf.count_tt τ f₂ :=
begin
  induction f₁ with c cs ih,
  { simp only [nil_append, count_tt_nil, zero_add] },
  { cases h : (c.eval τ); simp [h, ih, add_assoc] }
end

theorem count_ff_append : cnf.count_ff τ (f₁ ++ f₂) = cnf.count_ff τ f₁ + cnf.count_ff τ f₂ :=
begin
  induction f₁ with c cs ih,
  { simp only [nil_append, count_ff_nil, zero_add] },
  { cases h : (c.eval τ); simp [h, ih, add_assoc] }
end

end counting

/-! # vars -/
section vars

variables [decidable_eq V] {v : V} {c : clause V} {f f₁ f₂ : cnf V}

protected def vars : cnf V → finset V
| []        := ∅
| (c :: cs) := (c.vars) ∪ (vars cs)

@[simp] theorem vars_nil : cnf.vars ([] : cnf V) = ∅ := rfl

@[simp] theorem vars_singleton (c : clause V) : cnf.vars [c] = clause.vars c :=
by { unfold cnf.vars, rw finset.union_empty }

@[simp] theorem vars_cons (c : clause V) (f : cnf V) : cnf.vars (c :: f) = c.vars ∪ f.vars := rfl

theorem mem_vars_cons_of_mem_vars (c : clause V) : v ∈ f.vars → v ∈ cnf.vars (c :: f) :=
assume h, finset.mem_union.mpr (or.inr h)

@[simp] theorem vars_append (f₁ f₂ : cnf V) : cnf.vars (f₁ ++ f₂) = f₁.vars ∪ f₂.vars :=
begin
  induction f₁ with c cs ih,
  { simp only [empty_union, vars_nil, nil_append] },
  { simp only [cnf.vars, cons_append c cs f₂, ih, finset.union_assoc] }
end

theorem vars_perm : f₁ ~ f₂ → f₁.vars = f₂.vars :=
begin
  intro hp,
  induction hp with _ _ _ _ IH  x y _  _ _ _ _ _ IH₁ IH₂,
  { refl },
  { unfold cnf.vars, rw IH },
  { unfold cnf.vars,
    rw [← finset.union_assoc, ← finset.union_assoc, finset.union_comm y.vars x.vars] },
  { exact eq.trans IH₁ IH₂ }
end

@[simp] theorem vars_join {v : V} : ∀ ⦃L : list (cnf V)⦄, 
  v ∈ cnf.vars (join L) ↔ ∃ (F : cnf V), F ∈ L ∧ v ∈ cnf.vars F :=
begin
  intro L,
  induction L with F Fs ih,
  { simp only [join, vars_nil, not_mem_empty, not_mem_nil, false_and, exists_false] },
  { simp [ih, cnf.vars_append],
    split,
    { rintro (h | ⟨F, hf₁, hf₂⟩),
      { use [F, or.inl rfl, h] },
      { use [F, or.inr hf₁, hf₂] } },
    { rintro ⟨F, (rfl | hf₁), hf₂⟩,
      { exact or.inl hf₂ },
      { exact or.inr ⟨_, hf₁, hf₂⟩ } } }
end

theorem clause_vars_subset_of_vars_of_mem : c ∈ f → c.vars ⊆ f.vars :=
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

theorem mem_vars_iff_exists_mem_clause_and_mem : v ∈ f.vars ↔ ∃ (c : clause V), c ∈ f ∧ v ∈ c.vars :=
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
      { exact finset.mem_union_right _ (ih.mpr ⟨c, hc, hv⟩) } } }
end

theorem vars_subset_of_subset : f₁ ⊆ f₂ → (cnf.vars f₁) ⊆ (cnf.vars f₂) :=
begin
  intros h v hv,
  rcases cnf.mem_vars_iff_exists_mem_clause_and_mem.mp hv with ⟨c, hf, hvc⟩,
  exact clause_vars_subset_of_vars_of_mem (h hf) hvc
end

end vars

/-! # Equisatisfiability -/

def eqsat (f₁ f₂ : cnf V) := satisfiable f₁ ↔ satisfiable f₂

--notation f₁ ` ≈ ` f₂ := equisatisfiable f₁ f₂

@[refl] theorem eqsat.refl (f : cnf V) : eqsat f f := ⟨id, id⟩

@[symm] theorem eqsat.symm (f₁ f₂ : cnf V) : eqsat f₁ f₂ → eqsat f₂ f₁ := λ h, ⟨h.2, h.1⟩

@[trans] theorem eqsat.trans {f₁ f₂ f₃ : cnf V} : eqsat f₁ f₂ → eqsat f₂ f₃ → eqsat f₁ f₃ :=
λ h₁ h₂, ⟨λ h, h₂.1 (h₁.1 h), λ h, h₁.2 (h₂.2 h)⟩

open assignment

/-! # S-equivalence -/

def sequiv (F₁ F₂ : cnf V) (s : finset V) := ∀ τ, 
  ((∃ σ₁, F₁.eval σ₁ = tt ∧ (agree_on τ σ₁ s)) ↔ (∃ σ₂, F₂.eval σ₂ = tt ∧ (agree_on τ σ₂ s)))

@[refl] theorem sequiv.refl (F : cnf V) (s : finset V) : sequiv F F s :=
assume _, iff.rfl

@[symm] theorem sequiv.symm {F₁ F₂ : cnf V} {s : finset V} : sequiv F₁ F₂ s → sequiv F₂ F₁ s :=
assume h τ, (h τ).symm

@[trans] theorem sequiv.trans {F₁ F₂ F₃ : cnf V} {s : finset V} :
  sequiv F₁ F₂ s → sequiv F₂ F₃ s → sequiv F₁ F₃ s :=
assume h₁ h₂ τ, ⟨λ h, (h₂ τ).mp ((h₁ τ).mp h), λ h, (h₁ τ).mpr ((h₂ τ).mpr h)⟩

/-! # agree_on theorems -/

theorem eval_eq_of_agree_on [decidable_eq V] {τ₁ τ₂ : assignment V} {f : cnf V} :
  (agree_on τ₁ τ₂ f.vars) → f.eval τ₁ = f.eval τ₂ :=
begin
  intro h,
  cases hev : (cnf.eval τ₂ f),
  { apply eval_ff_iff_exists_clause_eval_ff.mpr,
    rcases eval_ff_iff_exists_clause_eval_ff.mp hev with ⟨c, hc, hff⟩,
    use [c, hc],
    exact hff ▸ clause.eval_eq_of_agree_on 
      (agree_on_subset (clause_vars_subset_of_vars_of_mem hc) h) },
  { apply eval_tt_iff_forall_clause_eval_tt.mpr,
    intros c hc,
    exact (eval_tt_iff_forall_clause_eval_tt.mp hev c hc) ▸ clause.eval_eq_of_agree_on
      (agree_on_subset (clause_vars_subset_of_vars_of_mem hc) h) }
end

end cnf