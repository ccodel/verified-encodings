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