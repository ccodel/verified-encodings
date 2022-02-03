/-
Defines the properties of assignments on polymorphic variables,
including equisatisfiability and equivalence on domains.

Authors: Cayden Codel, Jeremy Avigad, Marijn Heule
Carnegie Mellon University
-/

import data.finset.basic
import cnf.literal

universe u

-- Represents the parametric type of the variable stored in the literal
variables {V : Type u} [decidable_eq V] [inhabited V]

namespace assignment

open literal
open finset

/-! # Properties -/

instance : inhabited (assignment V) := ⟨(λ _, tt)⟩

/-! # Equisatisfiability -/

/- Formulas are functions from assignments to booleans.
   Two formulas are equisatisfiable if the satisfiability of one
   implies the satisfiability of the other.
-/
def eqsat (f₁ f₂ : assignment V → bool) : Prop := 
  (∃ (α₁ : assignment V), f₁ α₁ = tt) ↔ (∃ (α₂ : assignment V), f₂ α₂ = tt)

@[refl] theorem eqsat.refl (f : assignment V → bool) : eqsat f f := ⟨id, id⟩

@[symm] theorem eqsat.symm {f₁ f₂ : assignment V → bool} :
  eqsat f₁ f₂ → eqsat f₂ f₁ :=
assume h, ⟨λ heq, h.mpr heq, λ heq, h.mp heq⟩

theorem eqsat_comm {f₁ f₂ : assignment V → bool} :
  (eqsat f₁ f₂) ↔ (eqsat f₂ f₁) :=
⟨eqsat.symm, eqsat.symm⟩

@[trans] theorem eqsat.trans {f₁ f₂ f₃ : assignment V → bool} :
  eqsat f₁ f₂ → eqsat f₂ f₃ → eqsat f₁ f₃ :=
begin
  intros h₁ h₂,
  split,
  { intro h,
    exact h₂.mp (h₁.mp h) },
  { intro h,
    exact h₁.mpr (h₂.mpr h) }
end

/-! # Equivalence on domain -/

/- Two assignments are equivalent on a domain of variables if they agree
   on the truth value of that variable for all variables in the set.

   We choose finsets as our objects of interest because the domain of any
   formula is finite, so equivalences that extend beyond those domains are
   essentially irrelevant.
-/
def eqod (α₁ α₂ : assignment V) (s : finset V) : Prop := ∀ v ∈ s, α₁ v = α₂ v

-- TODO how to properly set up this notation so that () are not required
notation α₁ ` ≡` s `≡ ` α₂ := eqod α₁ α₂ s

@[refl] theorem eqod.refl (α : assignment V) (s : finset V) : α ≡s≡ α :=
by tautology

@[symm] theorem eqod.symm {α₁ α₂ : assignment V} {s : finset V} :
  (α₁ ≡s≡ α₂) → (α₂ ≡s≡ α₁) :=
assume h v hv, (h v hv).symm

theorem eqod_comm {α₁ α₂ : assignment V} {s : finset V} :
  (α₁ ≡s≡ α₂) ↔ (α₂ ≡s≡ α₁) :=
⟨eqod.symm, eqod.symm⟩

@[trans] theorem eqod.trans {α₁ α₂ α₃ : assignment V} {s : finset V} :
  (α₁ ≡s≡ α₂) → (α₂ ≡s≡ α₃) → (α₁ ≡s≡ α₃) :=
assume h₁ h₂ v hv, eq.trans (h₁ v hv) (h₂ v hv)

@[simp] theorem eqod_nil (α₁ α₂ : assignment V) : α₁ ≡∅≡ α₂ :=
assume v hv, absurd hv (not_mem_empty v)

theorem eqod_subset {α₁ α₂ : assignment V} {s₁ s₂ : finset V} :
  s₁ ⊆ s₂ → (α₁ ≡s₂≡ α₂) → (α₁ ≡s₁≡ α₂) :=
assume h hs₂ v hv, hs₂ v (h hv)

-- Can extend equivalence if equivalent on var
theorem eqod_union_of_eqod_of_eq {α₁ α₂ : assignment V} 
  {v : V} {s : finset V} :
  (α₁ ≡s≡ α₂) → α₁ v = α₂ v → (α₁ ≡({v} ∪ s)≡ α₂) :=
begin
  intros heqod heq u hu,
  rcases mem_union.mp hu with h | h,
  { rw mem_singleton at h, rw [h, heq] },
  { exact heqod u h }
end

-- Can also extend equivalence for unions of sets rather than singletons
theorem eqod_union {α₁ α₂ : assignment V} {s₁ s₂ : finset V} :
  (α₁ ≡s₁≡ α₂) → (α₁ ≡s₂≡ α₂) → (α₁ ≡(s₁ ∪ s₂)≡ α₂) :=
begin
  intros h₁ h₂ v hv,
  rcases mem_union.mp hv with h | h,
  { exact h₁ v h },
  { exact h₂ v h }
end

theorem eqod_inter {α₁ α₂ : assignment V} {s₁ s₂ : finset V} :
  (α₁ ≡s₁≡ α₂) → (α₁ ≡s₂≡ α₂) → (α₁ ≡(s₁ ∩ s₂)≡ α₂) :=
assume h₁ _ v hv, h₁ v (mem_inter.mp hv).1

theorem eqod_left_of_eqod_union {α₁ α₂ : assignment V} {s₁ s₂ : finset V} :
  (α₁ ≡(s₁ ∪ s₂)≡ α₂) → (α₁ ≡s₁≡ α₂) :=
assume h v hv, h v (mem_union_left s₂ hv)

theorem eqod_right_of_eqod_union {α₁ α₂ : assignment V} {s₁ s₂ : finset V} :
  (α₁ ≡(s₁ ∪ s₂)≡ α₂) → (α₁ ≡s₂≡ α₂) :=
assume h v hv, h v (mem_union_right s₁ hv)

/-! # Evaluation with eqod -/

theorem eval_eq_of_eqod_of_var_mem {α₁ α₂ : assignment V} 
  {s : finset V} {l : literal V} : 
  (α₁ ≡s≡ α₂) → l.var ∈ s → l.eval α₁ = l.eval α₂ :=
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
theorem exists_eqod_and_eq_of_not_mem
  {s : finset V} {v : V} (α₁ : assignment V) (b : bool) :
  v ∉ s → ∃ (α₂ : assignment V), (α₁ ≡s≡ α₂) ∧ α₂ v = b :=
begin
  intro hv,
  use (λ x, if x = v then b else α₁ x),
  simp [eqod],
  intros x hx,
  simp [ne_of_mem_of_not_mem hx hv]
end

-- The domain can be extended by whole finsets instead
theorem exists_eqod_and_eq_of_disjoint
  {s₁ s₂ : finset V} {α₁ : assignment V} (f : V → bool) :
  disjoint s₁ s₂ → ∃ (α₂ : assignment V), (α₁ ≡s₁≡ α₂) ∧ (∀ v ∈ s₂, α₂ v = f v) :=
begin
  intro h,
  use (λ x, if x ∈ s₂ then f x else α₁ x),
  simp [eqod],
  split,
  { intros v hv,
    simp [disjoint_left.mp h hv] },
  { intros v hv₁ hv₂,
    contradiction }
end

/-! # ite -/

-- When a variable is in the set, uses the first assignment. Else, the second.
protected def ite (s : finset V) (α₁ α₂ : assignment V) : assignment V :=
  λ v, if v ∈ s then α₁ v else α₂ v

@[simp] theorem ite_nil (α₁ α₂ : assignment V) (v : V) : 
  (assignment.ite ∅ α₁ α₂) v = α₂ v :=
by simp [assignment.ite]

theorem ite_pos (α₁ α₂ : assignment V) {s : finset V} {v : V} :
  v ∈ s → (assignment.ite s α₁ α₂) v = α₁ v :=
assume h, by simp [assignment.ite, h]

theorem ite_neg (α₁ α₂ : assignment V) {s : finset V} {v : V} :
  v ∉ s → (assignment.ite s α₁ α₂) v = α₂ v :=
assume h, by simp [assignment.ite, h]

theorem ite_pos_lit (α₁ α₂ : assignment V) {s : finset V} {l : literal V} :
  l.var ∈ s → literal.eval (assignment.ite s α₁ α₂) l = literal.eval α₁ l :=
begin
  cases l,
  { simp [literal.var, literal.eval], exact ite_pos α₁ α₂ },
  { simp [literal.var, literal.eval],
    intro h, rw ite_pos α₁ α₂ h }
end

theorem ite_neg_lit (α₁ α₂ : assignment V) {s : finset V} {l : literal V} :
  l.var ∉ s → literal.eval (assignment.ite s α₁ α₂) l = literal.eval α₂ l :=
begin
  cases l,
  { simp [literal.var, literal.eval], exact ite_neg α₁ α₂ },
  { simp [literal.var, literal.eval],
    intro h, rw ite_neg α₁ α₂ h }
end

theorem eqod_ite_of_disjoint (α₁ α₂ : assignment V) {s₁ s₂ : finset V} :
  disjoint s₁ s₂ → (α₂ ≡s₂≡ (assignment.ite s₁ α₁ α₂)) :=
assume h v hv, by simp [assignment.ite, disjoint_right.mp h hv]

theorem eqod_ite_of_subset (α₁ α₂ : assignment V) {s₁ s₂ : finset V} :
  s₂ ⊆ s₁ → (α₁ ≡s₂≡ (assignment.ite s₁ α₁ α₂)) :=
assume h v hv, by simp [assignment.ite, h hv]

/-! # Constant assignments -/

-- Constant function assignments
def all_tt : assignment V := (λ _, tt)
def all_ff : assignment V := (λ _, ff)

theorem all_tt_eval_tt : ∀ (v : V), all_tt v = tt := by simp [all_tt]
theorem all_ff_eval_ff : ∀ (v : V), all_ff v = ff := by simp [all_ff]

end assignment