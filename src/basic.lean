/-

  Some basic facts unrelated to literals, clauses, etc. that are useful for proofs.

  Author: Cayden Codel
  Carnegie Mellon University

-/

import data.bool

-- Define shorthand for XOR
notation a ⊕ b := bxor a b

-- Some trivial, useful theorems
@[simp] theorem bxor_tt_left  : ∀ a, bxor tt a = bnot a := dec_trivial
@[simp] theorem bxor_tt_right : ∀ a, bxor a tt = bnot a := dec_trivial

@[simp] theorem cond_tt_ff : ∀ a, cond a tt ff = a := dec_trivial
@[simp] theorem cond_ff_tt : ∀ a, cond a ff tt = bnot a := dec_trivial