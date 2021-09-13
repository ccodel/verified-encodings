/-

  Some basic facts unrelated to literals, clauses, etc. that are useful for proofs.

  Author: Cayden Codel
  Carnegie Mellon University

-/

import data.bool
import data.list.basic

open list

-- Define shorthand for XOR
notation a ⊕ b := bxor a b
--notation a ∨ b := bor a b
--notation a ∧ b := band a b

-- Some trivial, useful theorems
@[simp] theorem bxor_tt_left  : ∀ a, bxor tt a = bnot a := dec_trivial
@[simp] theorem bxor_tt_right : ∀ a, bxor a tt = bnot a := dec_trivial

@[simp] theorem cond_tt_ff : ∀ a, cond a tt ff = a := dec_trivial
@[simp] theorem cond_ff_tt : ∀ a, cond a ff tt = bnot a := dec_trivial

-- Expand xor in terms of other boolean operations
-- (Proof seems inane - shorten?)
theorem bxor_conjunctive : ∀ (a b : bool), bxor a b = (a || b) && (!a || !b)
| tt tt := dec_trivial
| tt ff := dec_trivial
| ff tt := dec_trivial
| ff ff := dec_trivial

theorem bxor_disjunctive : ∀ (a b : bool), bxor a b = (!a && b) || (a && !b)
| tt tt := dec_trivial
| tt ff := dec_trivial
| ff tt := dec_trivial
| ff ff := dec_trivial

theorem neq_of_ff_of_tt {a b : bool} : a = tt → b = ff → a ≠ b :=
begin
  intros ha hb, simp [ha, hb]
end

theorem bool_by_cases : ∀ (b : bool), b = tt ∨ b = ff
| tt := by { left, refl }
| ff := by { right, refl }

/- This is a shorthand for absurd that derives from a boolean that is true and false -/
theorem absurd_bool {a : bool} {b : Prop} : a = tt → a = ff → b :=
assume h₁ h₂, absurd h₁ (neq_of_ff_of_tt rfl h₂).symm

/- Reasoning about cond is helpful if the result of the cond is known -/
theorem cond_tt_of_cond_eq_first_of_ne {α : Type} [decidable_eq α] {a₁ a₂ : α} {b : bool} : 
  a₁ ≠ a₂ → cond b a₁ a₂ = a₁ → b = tt :=
begin
  intros hne hcond,
  rcases bool_by_cases b,
  { exact h },
  { simp [h] at hcond, exact absurd hcond (ne.symm hne) }
end

theorem cond_ff_of_cond_eq_second_of_ne {α : Type} [decidable_eq α] {a₁ a₂ : α} {b : bool} :
  a₁ ≠ a₂ → cond b a₁ a₂ = a₂ → b = ff :=
begin
  intros hne hcond,
  rcases bool_by_cases b,
  { simp [h] at hcond, exact absurd hcond hne },
  { exact h }
end

theorem list_by_cases {α : Type} : ∀ (l : list α), l = [] ∨ ∃ b L, l = b :: L
| []        := by { left, refl }
| (x :: xs) := by { right, use [x, xs] }

theorem ne_tail_of_eq_head_of_ne {α : Type} [decidable_eq α] {a b : α} : ∀ {l₁ : list α},
  ∀ {l₂ : list α}, (a :: l₁) ≠ (b :: l₂) → a = b → l₁ ≠ l₂
| []        := by simp
| (x :: xs) := begin
  intros l₂ hneq heq,
  by_contradiction,
  simp at h,
  exact absurd (congr (congr_arg cons heq) h) hneq
end

-- Some facts about map that help
theorem exists_of_map_singleton {α β : Type} {f : α → β} {b : β} :
  ∀ {l : list α}, map f l = [b] → ∃ a, [a] = l ∧ f a = b
| []        := by { contradiction }
| [x]       := by { simp [map_cons] }
| (x :: y :: ys) := by { simp }

theorem exists_cons_of_map_cons {α β : Type} {f : α → β} {b : β} {bs : list β} :
  ∀ {l : list α}, map f l = b :: bs → ∃ h L, l = h :: L ∧ f h = b ∧ map f L = bs
| []        := by { contradiction }
| (x :: xs) := begin 
  simp [map_cons],
  intros hx hxs,
  use x, use xs, simp [hx, hxs]
end

-- If instead the list from above is a map construction too
theorem exists_map_cons_of_map_cons {α β : Type} {f : α → β} {a : α} {as : list α} :
  ∀ {l : list α}, map f l = map f (a :: as) → ∃ h L, l = h :: L ∧ f h = f a ∧ map f L = map f as
| []        := by { contradiction }
| (x :: xs) := begin
  simp [map_cons],
  intros hx hxs,
  use [x, xs], simp [hx, hxs]
end

-- Or facts about filter
theorem length_filter {α : Type} {p : α → Prop} [decidable_pred p] {l : list α} : 
  length (filter p l) ≤ length l :=
begin
  induction l with x xs ih,
  { simp },
  { by_cases p x,
    { simp [filter_cons_of_pos _ h, ih] },
    { simp [filter_cons_of_neg _ h, ih, le_add_right] } }
end