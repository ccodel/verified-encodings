/-
Defines the properties of assignments on polymorphic variables,
including equisatisfiability and equivalence on domains.

Authors: Cayden Codel, Jeremy Avigad, Marijn Heule
Carnegie Mellon University
-/

import data.list.basic
import cnf.literal

universe u

-- Represents the parametric type of the variable stored in the literal
variables {V : Type u} [decidable_eq V] [inhabited V]

namespace assignment

open literal
open list

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
   on the truth value of that variable for all variables in the list.
-/
def eqod (α₁ α₂ : assignment V) (l : list V) : Prop := ∀ v ∈ l, α₁ v = α₂ v

-- Better notation for this?
notation α₁ ` ≡[`:50 l `]≡ `:50 α₂ := eqod α₁ α₂ l

@[refl] theorem eqod.refl (α : assignment V) (l : list V) : α ≡[l]≡ α :=
by simp [eqod]

@[symm] theorem eqod.symm {α₁ α₂ : assignment V} {l : list V} (p : α₁ ≡[l]≡ α₂) :
  α₂ ≡[l]≡ α₁ :=
assume v hv, (p v hv).symm

theorem eqod_comm {α₁ α₂ : assignment V} {l : list V} :
  (α₁ ≡[l]≡ α₂) ↔ (α₂ ≡[l]≡ α₁) :=
⟨eqod.symm, eqod.symm⟩

@[trans] theorem eqod.trans {α₁ α₂ α₃ : assignment V} {l : list V} :
  (α₁ ≡[l]≡ α₂) → (α₂ ≡[l]≡ α₃) → (α₁ ≡[l]≡ α₃) :=
assume h₁ h₂ v hv, eq.trans (h₁ v hv) (h₂ v hv)

@[simp] theorem eqod_nil (α₁ α₂ : assignment V) : α₁ ≡[nil]≡ α₂ :=
by simp [eqod]

-- If domains become sets instead of lists, then perms become moot
theorem eqod_perm {α₁ α₂ : assignment V} {l₁ l₂ : list V} :
  l₁ ~ l₂ → (α₁ ≡[l₁]≡ α₂) → α₁ ≡[l₂]≡ α₂ :=
assume h₁ h₂ v hv, h₂ v ((perm.mem_iff h₁).mpr hv)

theorem eqod_of_eqod_cons {α₁ α₂ : assignment V} {v : V} {l : list V} :
  (α₁ ≡[v :: l]≡ α₂) → α₁ ≡[l]≡ α₂ :=
by simp [eqod]

-- From the set point of view, we might want non-membership of new value v
theorem eqod_cons_of_eq_of_not_mem_of_eqod {α₁ α₂ : assignment V} {v : V} {l : list V} :
  (α₁ ≡[l]≡ α₂) → α₁ v = α₂ v → α₁ ≡[v :: l]≡ α₂ :=
begin
  intros h₁ heq m hm,
  rcases eq_or_mem_of_mem_cons hm with rfl | hml,
  { exact heq },
  { exact h₁ m hml }
end

theorem eqod_subset_of_eqod {α₁ α₂ : assignment V} {l₁ l₂ : list V} :
  l₁ ⊆ l₂ → (α₁ ≡[l₂]≡ α₂) → α₁ ≡[l₁]≡ α₂ :=
assume h₁ h₂ v hv, h₂ v (h₁ hv)

-- The types of mem_union don't check?
--theorem eqod_union_of_eqod [decidable_eq V] [has_union (list V)] [has_mem V (list V)] {α₁ α₂ : assignment V} {l₁ l₂ : list V} :
--  (α₁ ≡[l₁]≡ α₂) → (α₁ ≡[l₂]≡ α₂) → α₁ ≡[l₁ ∪ l₂]≡ α₂ :=
--assume h₁ h₂ v hv, by { cases (mem_union.mp hn), exact h₁ n h, exact h₂ n h }

-- Same thing here, with mem_inter
--theorem eqod_inter_of_eqod [has_inter (list V)] {α₁ α₂ : assignment V} {l₁ l₂ : list V} :
--  (α₁ ≡[l₁]≡ α₂) → (α₁ ≡[l₂]≡ α₂) → α₁ ≡[l₁ ∩ l₂]≡ α₂ :=
--assume h₁ _ v hv, h₁ v (mem_inter.mp hv).1

theorem eqod_append_left {α₁ α₂ : assignment V} {l₁ l₂ : list V} :
  (α₁ ≡[l₁ ++ l₂]≡ α₂) → α₁ ≡[l₁]≡ α₂ :=
assume h, eqod_subset_of_eqod (sublist.subset (sublist_append_left l₁ l₂)) h

theorem eqod_append_right {α₁ α₂ : assignment V} {l₁ l₂ : list V} :
  (α₁ ≡[l₁ ++ l₂]≡ α₂) → α₁ ≡[l₂]≡ α₂ :=
assume h, eqod_subset_of_eqod (sublist.subset (sublist_append_right l₁ l₂)) h

/-! # Evaluation and extension -/

theorem eval_eq_of_mem_of_eqod {α₁ α₂ : assignment V} {l : list V} {lit : literal V} :
  (α₁ ≡[l]≡ α₂) → lit.var ∈ l → literal.eval α₁ lit = literal.eval α₂ lit :=
by { cases lit; simp only [literal.eval, var]; intros h hl; simp only [h lit hl] }

-- Sometimes the domain of equivalence needs to be extended according to a particular assignment
theorem exists_extended_assignment_of_assignment [decidable_eq V] (α₁ : assignment V) {l : list V} {v : V} :
  v ∉ l → ∀ (b : bool), ∃ (α₂ : assignment V), (α₁ ≡[l]≡ α₂) ∧ α₂ v = b :=
begin
  intros hv b,
  use (λ (x : V), if x = v then b else α₁ x),
  simp [eqod],
  intros x hx,
  simp [ne_of_mem_of_not_mem hx hv]
end

-- The domain can be extended by whole lists instead
theorem exists_list_extended_assignment_of_assignment [decidable_eq V] (α₁ : assignment V) {l e : list V} :
  disjoint l e → ∀ (f : V → bool), ∃ (α₂ : assignment V), (α₁ ≡[l]≡ α₂) ∧ (∀ n ∈ e, α₂ n = f n) :=
begin
  intros hle f,
  use (λ x, if x ∈ e then f x else α₁ x),
  simp [eqod],
  split,
  { intros v hv, simp [hle hv] },
  { intros n ha hb, contradiction }
end

/-! # ite -/
-- A process by which membership of one set uses assignment 1, else assignment 2

protected def ite (α₁ α₂ : assignment V) (l : list V) : assignment V :=
  λ v, if v ∈ l then α₁ v else α₂ v

@[simp] theorem ite_nil (α₁ α₂ : assignment V) : 
  ∀ (v : V), (assignment.ite α₁ α₂ []) v = α₂ v :=
assume v, by simp [assignment.ite]

theorem ite_pos (α₁ α₂ : assignment V) {l : list V} {v : V} :
  v ∈ l → (assignment.ite α₁ α₂ l) v = α₁ v :=
assume h, by simp [assignment.ite, h]

theorem ite_neg (α₁ α₂ : assignment V) {l : list V} {v : V} :
  v ∉ l → (assignment.ite α₁ α₂ l) v = α₂ v :=
assume h, by simp [assignment.ite, h]

theorem ite_pos_of_lit (α₁ α₂ : assignment V) {l : list V} {lit : literal V} :
  lit.var ∈ l → literal.eval (assignment.ite α₁ α₂ l) lit = literal.eval α₁ lit :=
begin
  cases lit,
  { simp [literal.var, literal.eval], exact ite_pos α₁ α₂ },
  { simp [literal.var, literal.eval],
    assume h,
    rw ite_pos α₁ α₂ h }
end

theorem ite_neg_of_lit (α₁ α₂ : assignment V) {l : list V} {lit : literal V} :
  lit.var ∉ l → literal.eval (assignment.ite α₁ α₂ l) lit = literal.eval α₂ lit :=
begin
  cases lit,
  { simp [literal.var, literal.eval], exact ite_neg α₁ α₂ },
  { simp [literal.var, literal.eval],
    assume h,
    rw ite_neg α₁ α₂ h }
end

theorem eqod_ite_of_disjoint (α₁ α₂ : assignment V) {l₁ l₂ : list V} :
  disjoint l₁ l₂ → α₂ ≡[l₂]≡ (assignment.ite α₁ α₂ l₁) :=
assume h v hv, by simp [assignment.ite, disjoint_right.mp h hv]

theorem eqod_ite_of_subset (α₁ α₂ : assignment V) {l₁ l₂ : list V} :
  l₂ ⊆ l₁ → α₁ ≡[l₂]≡ (assignment.ite α₁ α₂ l₁) :=
assume h v hv, by simp [assignment.ite, h hv]

/-! # Miscellaneous -/

-- Constant function assignments
def all_tt : assignment V := (λ _, tt)
def all_ff : assignment V := (λ _, ff)

theorem all_tt_eval_tt : ∀ (n : V), all_tt n = tt := by simp [all_tt]
theorem all_ff_eval_ff : ∀ (n : V), all_ff n = ff := by simp [all_ff]

-- There may be times where setting or flipping variables is important
def set_var [decidable_eq V] (α : assignment V) (v : V) (b : bool) : assignment V :=
  λ x, if x = v then b else α x

def flip_var [decidable_eq V] (α : assignment V) (v : V) : assignment V :=
  λ x, if x = v then bnot (α v) else α x

theorem eval_eq_of_set_var {α : assignment V} {v : V} {b : bool} : 
  (set_var α v b) v = b :=
by simp [set_var]

theorem eval_ne_of_flip_var {α : assignment V} {v : V} :
  α v = bnot ((flip_var α v) v) :=
by simp [flip_var]

theorem eqod_set_var_of_not_mem (α : assignment V) (v : V) (b : bool) :
  ∀ (l : list V), v ∉ l → (α ≡[l]≡ (set_var α v b)) :=
begin
  intros l h,
  unfold set_var,
  intros z hz,
  simp [ne_of_mem_of_not_mem hz h]
end

end assignment