/-

  Some basic facts unrelated to literals, clauses, etc. that are useful for proofs.

  Author: Cayden Codel
  Carnegie Mellon University

-/

import data.bool
import data.list.basic

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

-- Some facts about map that help
theorem exists_cons_of_map_cons {α β : Type} {f : α → β} {b : β} {bs : list β} :
  ∀ {l : list α}, list.map f l = b :: bs → ∃ h L, l = h :: L ∧ f h = b ∧ list.map f L = bs
| [] := by { contradiction }
| (x :: xs) := begin 
  simp [list.map_cons],
  intros hx hxs, split,
  { use x, exact hx},
  { use xs, exact hxs}
end