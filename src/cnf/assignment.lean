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
variables {V : Type*} [decidable_eq V] [inhabited V]

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
notation τ₁ ` ≡` s `≡ ` τ₂ := eqod τ₁ τ₂ s

variables {τ₁ τ₂ τ₃ : assignment V} {s s₁ s₂ : finset V} {v : V} {l : literal V}

@[refl] theorem eqod.refl (τ : assignment V) (s : finset V) : τ ≡s≡ τ :=
by tautology

@[symm] theorem eqod.symm : (τ₁ ≡s≡ τ₂) → (τ₂ ≡s≡ τ₁) :=
assume h v hv, (h v hv).symm

theorem eqod_comm : (τ₁ ≡s≡ τ₂) ↔ (τ₂ ≡s≡ τ₁) :=
⟨eqod.symm, eqod.symm⟩

@[trans] theorem eqod.trans : (τ₁ ≡s≡ τ₂) → (τ₂ ≡s≡ τ₃) → (τ₁ ≡s≡ τ₃) :=
assume h₁ h₂ v hv, eq.trans (h₁ v hv) (h₂ v hv)

@[simp] theorem eqod_nil (τ₁ τ₂ : assignment V) : τ₁ ≡∅≡ τ₂ :=
assume v hv, absurd hv (not_mem_empty v)

theorem eqod_subset : s₁ ⊆ s₂ → (τ₁ ≡s₂≡ τ₂) → (τ₁ ≡s₁≡ τ₂) :=
assume h hs₂ v hv, hs₂ v (h hv)

-- Can extend equivalence if equivalent on var
theorem eqod_union_of_eqod_of_eq : 
  (τ₁ ≡s≡ τ₂) → τ₁ v = τ₂ v → (τ₁ ≡({v} ∪ s)≡ τ₂) :=
begin
  intros heqod heq u hu,
  rcases mem_union.mp hu with h | h,
  { rw mem_singleton at h, rw [h, heq] },
  { exact heqod u h }
end

-- Can also extend equivalence for unions of sets rather than singletons
theorem eqod_union : (τ₁ ≡s₁≡ τ₂) → (τ₁ ≡s₂≡ τ₂) → (τ₁ ≡(s₁ ∪ s₂)≡ τ₂) :=
begin
  intros h₁ h₂ v hv,
  rcases mem_union.mp hv with h | h,
  { exact h₁ v h },
  { exact h₂ v h }
end

theorem eqod_inter : (τ₁ ≡s₁≡ τ₂) → (τ₁ ≡s₂≡ τ₂) → (τ₁ ≡(s₁ ∩ s₂)≡ τ₂) :=
assume h₁ _ v hv, h₁ v (mem_inter.mp hv).1

theorem eqod_left_of_eqod_union : (τ₁ ≡(s₁ ∪ s₂)≡ τ₂) → (τ₁ ≡s₁≡ τ₂) :=
assume h v hv, h v (mem_union_left s₂ hv)

theorem eqod_right_of_eqod_union : (τ₁ ≡(s₁ ∪ s₂)≡ τ₂) → (τ₁ ≡s₂≡ τ₂) :=
assume h v hv, h v (mem_union_right s₁ hv)

/-! # Evaluation with eqod -/

theorem eval_eq_of_eqod_of_var_mem :
  (τ₁ ≡s≡ τ₂) → l.var ∈ s → l.eval τ₁ = l.eval τ₂ :=
begin
  cases l,
  { unfold var literal.eval,
    intros h hl,
    exact h l hl },
  { unfold var literal.eval,
    intros h hl,
    exact congr_arg bnot (h l hl) }
end

-- Rather than extending the equivalence, as in [eqod_union_of_eqod_of_eq],
-- sometimes we need to create an assignment that is equivalent 
-- and agrees on one more specified value
theorem exists_eqod_and_eq_of_not_mem (τ₁ : assignment V) (b : bool) :
  v ∉ s → ∃ τ₂, (τ₁ ≡s≡ τ₂) ∧ τ₂ v = b :=
begin
  intro hv,
  use (λ x, if x = v then b else τ₁ x),
  simp [eqod],
  intros x hx,
  simp [ne_of_mem_of_not_mem hx hv]
end

-- The domain can be extended by whole finsets instead
theorem exists_eqod_and_eq_of_disjoint (f : V → bool) :
  disjoint s₁ s₂ → ∃ τ₂, (τ₁ ≡s₁≡ τ₂) ∧ (∀ v ∈ s₂, τ₂ v = f v) :=
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

-- When a variable is in the set, uses the first assignment. Else, the second.
protected def ite (s : finset V) (τ₁ τ₂ : assignment V) : assignment V :=
  λ v, if v ∈ s then τ₁ v else τ₂ v

@[simp] theorem ite_nil : ∀ (τ₁ τ₂ : assignment V),
  (assignment.ite ∅ τ₁ τ₂) = τ₂ :=
by simp [assignment.ite]

theorem ite_pos {s : finset V} {v : V} :
  v ∈ s → ∀ (τ₁ τ₂ : assignment V), (assignment.ite s τ₁ τ₂) v = τ₁ v :=
assume h, by simp [assignment.ite, h]

theorem ite_neg {s : finset V} {v : V} :
  v ∉ s → ∀ (τ₁ τ₂ : assignment V), (assignment.ite s τ₁ τ₂) v = τ₂ v :=
assume h, by simp [assignment.ite, h]

theorem ite_pos_lit {s : finset V} {l : literal V} :
  l.var ∈ s → ∀ (τ₁ τ₂ : assignment V), 
  literal.eval (assignment.ite s τ₁ τ₂) l = literal.eval τ₁ l :=
begin
  cases l,
  { simp [literal.var, literal.eval], intro h, exact ite_pos h },
  { simp [literal.var, literal.eval],
    intros h _ _, rw ite_pos h }
end

theorem ite_neg_lit {s : finset V} {l : literal V} :
  l.var ∉ s → ∀ (τ₁ τ₂ : assignment V), 
  literal.eval (assignment.ite s τ₁ τ₂) l = literal.eval τ₂ l :=
begin
  cases l,
  { simp [literal.var, literal.eval], intro h, exact ite_neg h },
  { simp [literal.var, literal.eval],
    intros h _ _, rw ite_neg h }
end

theorem ite_eqod (s : finset V) (τ₁ τ₂ : assignment V) :
  (assignment.ite s τ₁ τ₂) ≡s≡ τ₁ :=
assume v hv, ite_pos hv _ _

theorem ite_eqod_of_disjoint (τ₁ τ₂ : assignment V) {s₁ s₂ : finset V} :
  disjoint s₁ s₂ → (τ₂ ≡s₂≡ (assignment.ite s₁ τ₁ τ₂)) :=
assume h v hv, by simp [assignment.ite, disjoint_right.mp h hv]

theorem ite_eqod_of_subset (τ₁ τ₂ : assignment V) {s₁ s₂ : finset V} :
  s₂ ⊆ s₁ → (τ₁ ≡s₂≡ (assignment.ite s₁ τ₁ τ₂)) :=
assume h v hv, by simp [assignment.ite, h hv]

-- TODO make similar theorems into rewrite rules rather than require input
theorem ite_eq_second_of_eqod {τ₁ τ₂ : assignment V} {s : finset V} :
  (τ₁ ≡s≡ τ₂) → assignment.ite s τ₁ τ₂ = τ₂ :=
begin
  intro h,
  apply function.funext_iff.mpr,
  intro v,
  by_cases hv : v ∈ s,
  { rw ite_pos hv _ _,
    exact h v hv },
  { rw ite_neg hv _ _ }
end

/-! # Constant assignments -/

-- Constant function assignments
def all_tt : assignment V := (λ _, tt)
def all_ff : assignment V := (λ _, ff)

theorem all_tt_eval_tt : ∀ (v : V), all_tt v = tt := by simp [all_tt]
theorem all_ff_eval_ff : ∀ (v : V), all_ff v = ff := by simp [all_ff]

end assignment