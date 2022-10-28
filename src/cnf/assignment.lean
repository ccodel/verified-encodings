/-
Defines the properties of assignments on polymorphic variables,
including equisatisfiability and equivalence on domains.

Authors: Cayden Codel, Jeremy Avigad, Marijn Heule
Carnegie Mellon University
-/

import data.finset.basic
import cnf.literal

universe u

-- Represents the type of the variable stored in the literal
variables {V : Type*}

namespace assignment

open literal
open finset

/-! # Properties -/

instance : inhabited (assignment V) := ⟨(λ _, tt)⟩

/-! # Equivalence on domain -/
section eqod

/- Two assignments are equivalent on a domain of variables if they agree
   on the truth value of that variable for all variables in the set.

   We choose finsets as our objects of interest because the domain of any
   formula is finite, so equivalences that extend beyond those domains are
   essentially irrelevant.
-/
def eqod (τ₁ τ₂ : assignment V) (s : finset V) : Prop := ∀ v ∈ s, τ₁ v = τ₂ v

-- TODO how to properly set up this notation so that () are not required
notation τ₁ ` ≡`:50 s `≡ `:40 τ₂ := eqod τ₁ τ₂ s

variables {τ₁ τ₂ τ₃ : assignment V} {s s₁ s₂ : finset V} {v : V} {l : literal V}

@[refl] theorem eqod.refl (τ : assignment V) (s : finset V) : eqod τ τ s :=
by tautology

@[symm] theorem eqod.symm : (eqod τ₁ τ₂ s) → (eqod τ₂ τ₁ s) :=
assume h v hv, (h v hv).symm

theorem eqod_comm : (eqod τ₁ τ₂ s) ↔ (eqod τ₂ τ₁ s) :=
⟨eqod.symm, eqod.symm⟩

@[trans] theorem eqod.trans : (eqod τ₁ τ₂ s) → (eqod τ₂ τ₃ s) → (eqod τ₁ τ₃ s) :=
assume h₁ h₂ v hv, eq.trans (h₁ v hv) (h₂ v hv)

@[simp] theorem eqod_nil (τ₁ τ₂ : assignment V) : eqod τ₁ τ₂ ∅ :=
assume v hv, absurd hv (not_mem_empty v)

theorem eqod_subset : s₁ ⊆ s₂ → (eqod τ₁ τ₂ s₂) → (eqod τ₁ τ₂ s₁) :=
assume h hs₂ v hv, hs₂ v (h hv)

section -- Need decidable_eq

variable [decidable_eq V]

theorem eqod_union_of_eqod_of_eq : (eqod τ₁ τ₂ s) → τ₁ v = τ₂ v → (eqod τ₁ τ₂ ({v} ∪ s)) :=
assume heqod heq u hu, or.elim (mem_union.mp hu)
  (λ h, (mem_singleton.mp h).symm ▸ heq) 
  (λ h, heqod u h)

theorem eqod_union : (eqod τ₁ τ₂ s₁) → (eqod τ₁ τ₂ s₂) → (eqod τ₁ τ₂ (s₁ ∪ s₂)) :=
assume h₁ h₂ v hv, or.elim (mem_union.mp hv) (λ h, h₁ v h) (λ h, h₂ v h)

theorem eqod_inter : (eqod τ₁ τ₂ s₁) → (eqod τ₁ τ₂ s₂) → (eqod τ₁ τ₂ (s₁ ∩ s₂)) :=
assume h₁ _ v hv, h₁ v (mem_inter.mp hv).1

theorem eqod_union_left : (eqod τ₁ τ₂ (s₁ ∪ s₂)) → (eqod τ₁ τ₂ s₁) :=
assume h v hv, h v (mem_union_left s₂ hv)

theorem eqod_union_right : (eqod τ₁ τ₂ (s₁ ∪ s₂)) → (eqod τ₁ τ₂ s₂) :=
assume h v hv, h v (mem_union_right s₁ hv)

end /- section -/

/-! # Evaluation with eqod -/

theorem eval_eq_of_eqod_of_var_mem : (eqod τ₁ τ₂ s) → l.var ∈ s → l.eval τ₁ = l.eval τ₂ :=
assume h₁ h₂, by { cases l, exact h₁ l h₂, exact congr_arg bnot (h₁ l h₂) }

-- We can extend eqod's by setting the truth value of a new variable
theorem exists_eqod_and_eq_of_not_mem [decidable_eq V] (τ₁ : assignment V) (b) :
  v ∉ s → ∃ τ₂, (eqod τ₁ τ₂ s) ∧ τ₂ v = b :=
begin
  intro hv,
  use (λ x, if x = v then b else τ₁ x),
  simp [eqod],
  intros x hx,
  simp [ne_of_mem_of_not_mem hx hv]
end

-- The domain can be extended by whole finsets, too
theorem exists_eqod_and_eq_of_disjoint [decidable_eq V] (f : V → bool) :
  disjoint s₁ s₂ → ∃ τ₂, (eqod τ₁ τ₂ s₁) ∧ (∀ v ∈ s₂, τ₂ v = f v) :=
begin
  intro h,
  use (λ x, if x ∈ s₂ then f x else τ₁ x),
  simp [eqod],
  split,
  { intros v hv,
    simp [disjoint_left.mp h hv] },
  { intros v hv₁ hv₂,
    contradiction }
end

end eqod

/-! # ite -/
section ite

variable [decidable_eq V]

-- When a variable is in the set, use the first assignment. Else, the second.
protected def ite (s : finset V) (τ₁ τ₂ : assignment V) : assignment V :=
  λ v, if v ∈ s then τ₁ v else τ₂ v

@[simp] theorem ite_nil : ∀ (τ₁ τ₂ : assignment V), (assignment.ite ∅ τ₁ τ₂) = τ₂ :=
by simp [assignment.ite]

theorem ite_pos {s : finset V} {v : V} : v ∈ s → ∀ (τ₁ τ₂), (assignment.ite s τ₁ τ₂) v = τ₁ v :=
assume h, by simp [assignment.ite, h]

theorem ite_neg {s : finset V} {v : V} : v ∉ s → ∀ (τ₁ τ₂), (assignment.ite s τ₁ τ₂) v = τ₂ v :=
assume h, by simp [assignment.ite, h]

theorem ite_pos_lit {s : finset V} {l : literal V} :
  l.var ∈ s → ∀ (τ₁ τ₂), l.eval (assignment.ite s τ₁ τ₂) = l.eval τ₁ :=
by { cases l,
     { simp [literal.var, literal.eval], exact ite_pos },
     { simp [literal.var, literal.eval], intros h _ _, rw ite_pos h } }

theorem ite_neg_lit {s : finset V} {l : literal V} :
  l.var ∉ s → ∀ (τ₁ τ₂), l.eval (assignment.ite s τ₁ τ₂) = l.eval τ₂ :=
by { cases l,
     { simp [literal.var, literal.eval], exact ite_neg },
     { simp [literal.var, literal.eval], intros h _ _, rw ite_neg h } }

theorem ite_eqod (s : finset V) (τ₁ τ₂ : assignment V) : eqod (assignment.ite s τ₁ τ₂) τ₁ s :=
assume v hv, ite_pos hv _ _

theorem ite_eqod_of_disjoint (τ₁ τ₂ : assignment V) {s₁ s₂ : finset V} :
  disjoint s₁ s₂ → (eqod τ₂ (assignment.ite s₁ τ₁ τ₂) s₂) :=
assume h v hv, by simp [assignment.ite, disjoint_right.mp h hv]

theorem ite_eqod_of_subset (τ₁ τ₂ : assignment V) {s₁ s₂ : finset V} :
  s₂ ⊆ s₁ → (eqod τ₁ (assignment.ite s₁ τ₁ τ₂) s₂) :=
assume h v hv, by simp [assignment.ite, h hv]

theorem ite_eq_second_of_eqod {τ₁ τ₂ : assignment V} {s : finset V} :
  (eqod τ₁ τ₂ s) → assignment.ite s τ₁ τ₂ = τ₂ :=
begin
  intro h,
  apply function.funext_iff.mpr,
  intro v,
  by_cases hv : v ∈ s,
  { rw ite_pos hv _ _, exact h v hv },
  { rw ite_neg hv _ _ }
end

end ite

/-! # Constant assignments -/

-- Constant function assignments
def all_tt : assignment V := (λ _, tt)
def all_ff : assignment V := (λ _, ff)

theorem all_tt_eval_tt : ∀ (v : V), all_tt v = tt := by simp [all_tt]
theorem all_ff_eval_ff : ∀ (v : V), all_ff v = ff := by simp [all_ff]

end assignment