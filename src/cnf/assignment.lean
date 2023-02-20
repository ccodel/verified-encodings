/-
Defines the properties of assignments on polymorphic variables,
including equisatisfiability and equivalence on domains.

Authors: Cayden Codel, Jeremy Avigad, Marijn Heule
Carnegie Mellon University
-/

import data.finset.basic
import cnf.literal

-- Represents the type of the variable stored in the literal
variables {V : Type*}

namespace assignment

open literal
open finset

/-! # Properties -/

instance : inhabited (assignment V) := ⟨(λ _, tt)⟩

section agree_on

/- Since the type of assignments makes every assignment a full map, we often
   restrict the set of variables under consideration to a finite set. To
   construct assignments that extend another, we instead use a notion of
   agreement on those finite sets.
-/
def agree_on (τ₁ τ₂ : assignment V) (s : finset V) : Prop := ∀ v ∈ s, τ₁ v = τ₂ v

-- TODO how to properly set up this notation so that () are not required
--notation τ₁ ` ≡`:50 s `≡ `:40 τ₂ := agree_on τ₁ τ₂ s

variables {τ₁ τ₂ τ₃ : assignment V} {s s₁ s₂ : finset V} {v : V} {l : literal V}

@[refl] theorem agree_on.refl (τ : assignment V) (s : finset V) : agree_on τ τ s :=
by tautology

@[symm] theorem agree_on.symm : (agree_on τ₁ τ₂ s) → (agree_on τ₂ τ₁ s) :=
assume h v hv, (h v hv).symm

theorem agree_on_comm : (agree_on τ₁ τ₂ s) ↔ (agree_on τ₂ τ₁ s) :=
⟨agree_on.symm, agree_on.symm⟩

@[trans] theorem agree_on.trans : (agree_on τ₁ τ₂ s) → (agree_on τ₂ τ₃ s) → (agree_on τ₁ τ₃ s) :=
assume h₁ h₂ v hv, eq.trans (h₁ v hv) (h₂ v hv)

@[simp] theorem agree_on_nil (τ₁ τ₂ : assignment V) : agree_on τ₁ τ₂ ∅ :=
assume v hv, absurd hv (not_mem_empty v)

theorem agree_on_subset : s₁ ⊆ s₂ → (agree_on τ₁ τ₂ s₂) → (agree_on τ₁ τ₂ s₁) :=
assume h hs₂ v hv, hs₂ v (h hv)

section agree_on_lemmas

variable [decidable_eq V]

theorem agree_on_union_of_agree_on_of_eq : (agree_on τ₁ τ₂ s) → τ₁ v = τ₂ v → (agree_on τ₁ τ₂ ({v} ∪ s)) :=
assume hagree_on heq u hu, or.elim (mem_union.mp hu)
  (λ h, (mem_singleton.mp h).symm ▸ heq) 
  (λ h, hagree_on u h)

theorem agree_on_union : (agree_on τ₁ τ₂ s₁) → (agree_on τ₁ τ₂ s₂) → (agree_on τ₁ τ₂ (s₁ ∪ s₂)) :=
assume h₁ h₂ v hv, or.elim (mem_union.mp hv) (λ h, h₁ v h) (λ h, h₂ v h)

theorem agree_on_inter : (agree_on τ₁ τ₂ s₁) → (agree_on τ₁ τ₂ s₂) → (agree_on τ₁ τ₂ (s₁ ∩ s₂)) :=
assume h₁ _ v hv, h₁ v (mem_inter.mp hv).1

theorem agree_on_union_left : (agree_on τ₁ τ₂ (s₁ ∪ s₂)) → (agree_on τ₁ τ₂ s₁) :=
assume h v hv, h v (mem_union_left s₂ hv)

theorem agree_on_union_right : (agree_on τ₁ τ₂ (s₁ ∪ s₂)) → (agree_on τ₁ τ₂ s₂) :=
assume h v hv, h v (mem_union_right s₁ hv)

end agree_on_lemmas

/-! # Evaluation with agree_on -/

theorem eval_eq_of_agree_on_of_var_mem : (agree_on τ₁ τ₂ s) → l.var ∈ s → l.eval τ₁ = l.eval τ₂ :=
assume h₁ h₂, by { cases l, exact h₁ l h₂, exact congr_arg bnot (h₁ l h₂) }

-- We can extend agree_on's by setting the truth value of a new variable
theorem exists_agree_on_and_eq_of_not_mem [decidable_eq V] (τ₁ : assignment V) (b) :
  v ∉ s → ∃ τ₂, (agree_on τ₁ τ₂ s) ∧ τ₂ v = b :=
begin
  intro hv,
  use (λ x, if x = v then b else τ₁ x),
  simp [agree_on],
  intros x hx,
  simp [ne_of_mem_of_not_mem hx hv]
end

-- The domain can be extended by whole finsets, too
theorem exists_agree_on_and_eq_of_disjoint [decidable_eq V] (f : V → bool) :
  disjoint s₁ s₂ → ∃ τ₂, (agree_on τ₁ τ₂ s₁) ∧ (∀ v ∈ s₂, τ₂ v = f v) :=
begin
  intro h,
  use (λ x, if x ∈ s₂ then f x else τ₁ x),
  simp [agree_on],
  split,
  { intros v hv,
    simp [disjoint_left.mp h hv] },
  { intros v hv₁ hv₂,
    contradiction }
end

end agree_on

/-! # aite -/
section aite

variable [decidable_eq V]

-- Defines a new assignment that uses τ₁ if the variable is in a set, τ₂ otherwise
-- aite is short for "assignment if-then-else"
def aite (s : finset V) (τ₁ τ₂ : assignment V) : assignment V :=
  λ v, if v ∈ s then τ₁ v else τ₂ v

@[simp] theorem aite_nil : ∀ (τ₁ τ₂ : assignment V), (aite ∅ τ₁ τ₂) = τ₂ :=
by simp [aite]

theorem aite_pos {s : finset V} {v : V} : v ∈ s → ∀ (τ₁ τ₂), (aite s τ₁ τ₂) v = τ₁ v :=
assume h, by simp [aite, h]

theorem aite_neg {s : finset V} {v : V} : v ∉ s → ∀ (τ₁ τ₂), (aite s τ₁ τ₂) v = τ₂ v :=
assume h, by simp [aite, h]

theorem aite_pos_lit {s : finset V} {l : literal V} :
  l.var ∈ s → ∀ (τ₁ τ₂), l.eval (aite s τ₁ τ₂) = l.eval τ₁ :=
by { cases l,
     { simp [literal.var, literal.eval], exact aite_pos },
     { simp [literal.var, literal.eval], intros h _ _, rw aite_pos h } }

theorem aite_neg_lit {s : finset V} {l : literal V} :
  l.var ∉ s → ∀ (τ₁ τ₂), l.eval (aite s τ₁ τ₂) = l.eval τ₂ :=
by { cases l,
     { simp [literal.var, literal.eval], exact aite_neg },
     { simp [literal.var, literal.eval], intros h _ _, rw aite_neg h } }

theorem aite_agree_on (s : finset V) (τ₁ τ₂ : assignment V) : agree_on (aite s τ₁ τ₂) τ₁ s :=
assume v hv, aite_pos hv _ _

theorem aite_agree_on_of_disjoint (τ₁ τ₂ : assignment V) {s₁ s₂ : finset V} :
  disjoint s₁ s₂ → (agree_on τ₂ (aite s₁ τ₁ τ₂) s₂) :=
assume h v hv, by simp [aite, disjoint_right.mp h hv]

theorem aite_agree_on_of_subset (τ₁ τ₂ : assignment V) {s₁ s₂ : finset V} :
  s₂ ⊆ s₁ → (agree_on τ₁ (aite s₁ τ₁ τ₂) s₂) :=
assume h v hv, by simp [aite, h hv]

theorem aite_agree_on_of_agree_on_of_agree_on {s : finset V} {τ σ₁ σ₂ : assignment V} :
  agree_on τ σ₁ s → agree_on τ σ₂ s → ∀ (t : finset V), agree_on τ (aite t σ₁ σ₂) s :=
begin
  intros h₁ h₂ t v hv,
  by_cases ht : v ∈ t,
  { rw aite_pos ht, exact h₁ v hv },
  { rw aite_neg ht, exact h₂ v hv }
end

theorem aite_eq_second_of_agree_on {τ₁ τ₂ : assignment V} {s : finset V} :
  (agree_on τ₁ τ₂ s) → aite s τ₁ τ₂ = τ₂ :=
begin
  intro h,
  apply function.funext_iff.mpr,
  intro v,
  by_cases hv : v ∈ s,
  { rw aite_pos hv _ _, exact h v hv },
  { rw aite_neg hv _ _ }
end

end aite

/-! # Constant assignments -/

-- Constant function assignments
@[reducible] def all_tt : assignment V := (λ _, tt)
@[reducible] def all_ff : assignment V := (λ _, ff)

theorem all_tt_eval_tt : ∀ (v : V), all_tt v = tt := by simp
theorem all_ff_eval_ff : ∀ (v : V), all_ff v = ff := by simp

end assignment