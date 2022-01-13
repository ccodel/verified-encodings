/-
This file expands on the definition for assignment given in literal.lean

Also defines equivalence on domains for assignments.

Authors: Cayden Codel, Jeremy Avigad, Marijn Heule
Carnegie Mellon University
-/

import cnf.literal

import data.list.basic
import data.list.perm

namespace assignment

open literal
open list

instance : inhabited assignment := ⟨(λ _, tt)⟩

/-! # Equivalence on domain definition -/

-- Making the ∀ n ∈ l into ∀ {n : nat}, n ∈ l is hard because sometimes the types don't agree
def eqod (α₁ α₂ : assignment) (l : list nat) : Prop := ∀ n ∈ l, α₁ n = α₂ n

notation α₁ ` ≡[`:50 l `]≡ `:50 α₂ := eqod α₁ α₂ l

/-! # Equivalence relation proofs -/

@[refl] theorem eqod.refl (α : assignment) (l : list nat) : α ≡[l]≡ α :=
by simp [eqod]

@[symm] theorem eqod.symm {α₁ α₂ : assignment} {l : list nat} (p : α₁ ≡[l]≡ α₂) :
  α₂ ≡[l]≡ α₁ :=
assume n hn, (p n hn).symm

theorem eqod_comm {α₁ α₂ : assignment} {l : list nat} :
  (α₁ ≡[l]≡ α₂) ↔ (α₂ ≡[l]≡ α₁) :=
⟨eqod.symm, eqod.symm⟩

@[trans] theorem eqod.trans {α₁ α₂ α₃ : assignment} {l : list nat} :
  (α₁ ≡[l]≡ α₂) → (α₂ ≡[l]≡ α₃) → (α₁ ≡[l]≡ α₃) :=
assume h₁ h₂ n hn, eq.trans (h₁ n hn) (h₂ n hn)

/-! # General properties -/
-- Many of these are general list properties, so the proofs are very short

@[simp] theorem eqod_nil (α₁ α₂ : assignment) : α₁ ≡[nil]≡ α₂ :=
by simp [eqod]

-- This could get its own section? If domains become sets instead of lists, then moot
theorem eqod_perm {α₁ α₂ : assignment} {l₁ l₂ : list nat} :
  l₁ ~ l₂ → (α₁ ≡[l₁]≡ α₂) → α₁ ≡[l₂]≡ α₂ :=
assume h₁ h₂ n hn, h₂ n ((perm.mem_iff h₁).mpr hn)

theorem eqod_of_eqod_cons {α₁ α₂ : assignment} {n : nat} {l : list nat} :
  (α₁ ≡[n :: l]≡ α₂) → α₁ ≡[l]≡ α₂ :=
by simp [eqod]

-- If two assignments agree on a value outside the domain, it can be extended
theorem eqod_cons_of_eq_of_not_mem_of_eqod {α₁ α₂ : assignment} {n : nat} {l : list nat} :
  (α₁ ≡[l]≡ α₂) → n ∉ l → α₁ n = α₂ n → α₁ ≡[n :: l]≡ α₂ :=
begin
  intros h₁ hnm heq m hm,
  rcases eq_or_mem_of_mem_cons hm with rfl | hml,
  { exact heq },
  { exact h₁ m hml }
end

theorem eqod_subset_of_eqod {α₁ α₂ : assignment} {l₁ l₂ : list nat} :
  l₁ ⊆ l₂ → (α₁ ≡[l₂]≡ α₂) → α₁ ≡[l₁]≡ α₂ :=
assume h₁ h₂ n hn, h₂ n (h₁ hn)

theorem eqod_union_of_eqod {α₁ α₂ : assignment} {l₁ l₂ : list nat} :
  (α₁ ≡[l₁]≡ α₂) → (α₁ ≡[l₂]≡ α₂) → α₁ ≡[l₁ ∪ l₂]≡ α₂ :=
assume h₁ h₂ n hn, by { cases (mem_union.mp hn), exact h₁ n h, exact h₂ n h }

theorem eqod_inter_of_eqod {α₁ α₂ : assignment} {l₁ l₂ : list nat} :
  (α₁ ≡[l₁]≡ α₂) → (α₁ ≡[l₂]≡ α₂) → α₁ ≡[l₁ ∩ l₂]≡ α₂ :=
assume h₁ _ n hn, h₁ n (mem_inter.mp hn).1

theorem eqod_append_left {α₁ α₂ : assignment} {l₁ l₂ : list nat} :
  (α₁ ≡[l₁ ++ l₂]≡ α₂) → α₁ ≡[l₁]≡ α₂ :=
assume h, eqod_subset_of_eqod (sublist.subset (sublist_append_left l₁ l₂)) h

theorem eqod_append_right {α₁ α₂ : assignment} {l₁ l₂ : list nat} :
  (α₁ ≡[l₁ ++ l₂]≡ α₂) → α₁ ≡[l₂]≡ α₂ :=
assume h, eqod_subset_of_eqod (sublist.subset (sublist_append_right l₁ l₂)) h

/-! # Evaluation and extension -/

theorem eval_eq_of_mem_of_eqod {α₁ α₂ : assignment} {ns : list nat} {l : literal} :
  (α₁ ≡[ns]≡ α₂) → l.var ∈ ns → literal.eval α₁ l = literal.eval α₂ l :=
by { cases l; simp only [literal.eval, var]; intros h hl; simp [h l hl] }

-- Sometimes the domain of equivalence needs to be extended according to a particular assignment
theorem exists_extended_assignment_of_assignment (α₁ : assignment) {l : list nat} {n : nat} :
  n ∉ l → ∀ (b : bool), ∃ (α₂ : assignment), (α₁ ≡[l]≡ α₂) ∧ α₂ n = b :=
begin
  intros hn b,
  use (λ x, if x = n then b else α₁ x),
  simp [eqod],
  intros x hx,
  simp [ne_of_mem_of_not_mem hx hn]
end

-- The domain can be extended by whole lists
theorem exists_list_extended_assignment_of_assignment (α₁ : assignment) {l e : list nat} :
  disjoint l e → ∀ (f : nat → bool), ∃ (α₂ : assignment), (α₁ ≡[l]≡ α₂) ∧ (∀ n ∈ e, α₂ n = f n) :=
begin
  intros hle f,
  use (λ x, if x ∈ e then f x else α₁ x),
  simp [eqod],
  split,
  { intros n hn, simp [hle hn] },
  { intros n ha hb, contradiction }
end

/-! # Append -/

-- When two domains are disjoint, their combination are equivalent on each respective domain
def append (α₁ α₂ : assignment) (l₁ l₂ : list nat) (h : disjoint l₁ l₂) :=
  (λ n, if n ∈ l₁ then α₁ n else α₂ n)

theorem append_eval_left_of_mem_left (α₁ α₂ : assignment) {l₁ l₂ : list nat} (h : disjoint l₁ l₂) {n : nat} :
  n ∈ l₁ → (append α₁ α₂ l₁ l₂ h) n = α₁ n :=
begin
  intro hn,
  simp [append, disjoint_left.mp h hn],
  intro hf,
  exact absurd hn hf
end

theorem append_eval_left_of_not_mem_left (α₁ α₂ : assignment) {l₁ l₂ : list nat} (h : disjoint l₁ l₂) {n : nat} :
  n ∉ l₁ → (append α₁ α₂ l₁ l₂ h) n = α₂ n :=
begin
  intro h,
  simp [append, h]
end

theorem append_eval_right_of_mem_right (α₁ α₂ : assignment) {l₁ l₂ : list nat} (h : disjoint l₁ l₂) {n : nat} :
  n ∈ l₂ → (append α₁ α₂ l₁ l₂ h) n = α₂ n :=
begin
  intro hn,
  simp [append, disjoint_right.mp h hn]
end

theorem eqod_of_append_left (α₁ α₂ : assignment) {l₁ l₂ : list nat} (h : disjoint l₁ l₂) :
  (append α₁ α₂ l₁ l₂ h) ≡[l₁]≡ α₁ :=
assume n hn, append_eval_left_of_mem_left α₁ α₂ h hn

theorem eqod_of_append_right (α₁ α₂ : assignment) {l₁ l₂ : list nat} (h : disjoint l₁ l₂) :
  (append α₁ α₂ l₁ l₂ h) ≡[l₂]≡ α₂ :=
assume n hn, append_eval_right_of_mem_right α₁ α₂ h hn

/-! # Miscellaneous -/

-- Constant function assignments
def all_tt : assignment := (λ _, tt)
def all_ff : assignment := (λ _, ff)

theorem all_tt_eval_tt : ∀ (n : nat), all_tt n = tt := by simp [all_tt]
theorem all_ff_eval_ff : ∀ (n : nat), all_ff n = ff := by simp [all_ff]

-- There may be times where setting or flipping variables is important
def set_var (α : assignment) (n : nat) (b : bool) : assignment :=
  λ x, if x = n then b else α x

def flip_var (α : assignment) (n : nat) : assignment :=
  λ x, if x = n then bnot (α n) else α x

theorem eval_eq_of_set_var {α : assignment} {n : nat} {b : bool} : (set_var α n b) n = b :=
by simp [set_var]

theorem eval_ne_of_flip_var {α : assignment} {n : nat} : α n = bnot ((flip_var α n) n) :=
by simp [flip_var]

end assignment