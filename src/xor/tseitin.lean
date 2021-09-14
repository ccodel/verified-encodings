/-
This file contains the development of the Tseitin encoding for XOR

Authors: Cayden Codel, Jeremy Avidgad, Marijn Heule
Carnegie Mellon University
-/

import cnf.literal
import cnf.clause
import cnf.cnf
import xor.xor

import data.list.basic
import data.list.min_max

open literal
open clause
open cnf
open xor_gate

open list

namespace tseitin_xor

lemma dropn_len {α : Type} {n : nat} {a : α} {l : list α} : n > 1 → length l > n → length (l.drop n ++ [a]) < length l :=
begin
  intros hn hl,
  induction l with x xs ih,
  { simp [lt_trans hn hl] at hl, contradiction },
  { by_cases length xs = n,
    { simp [h, gt.lt hn] },
    { simp at hl,
      have red := ih (gt.lt (array.push_back_idx hl (ne.symm h))), -- strange theorem
      simp [nat.sub_add_eq_add_sub (nat.lt_succ_iff.mp hl)] at red,
      simp [red] } }
end

-- We start with the instance of pooling number n = 3
-- The n provided is the greatest element in l, so that new variables can be created
-- The well_founded had to be used because of the growing n variable
-- Unfold didn't work until I provided a nil case - intentional?
def tseitin_xor3 : list literal → nat → cnf
| [] _ := [[]]
| l n := 
    if h : length l ≤ 3 then xor_cnf l
    else
      have length (l.drop 3 ++ [Pos (n + 1)]) < length l, 
        from (dropn_len (nat.succ 0).one_lt_succ_succ (not_le.mp h)),
      xor_cnf (l.take 3 ++ [Neg (n + 1)]) ++ (tseitin_xor3 (l.drop 3 ++ [Pos (n + 1)]) (n + 1))
using_well_founded {
  rel_tac := λ a b, `[exact ⟨_, measure_wf (λ σ, list.length σ.fst)⟩],
  dec_tac := tactic.assumption
}

lemma tseitin_xor3_base_case {ls : list literal} (n : nat) (h : length ls ≤ 3) :
  tseitin_xor3 ls n = xor_cnf ls :=
begin
  rcases list_by_cases ls with (rfl | ⟨l, ls, rfl⟩),
  { simp [tseitin_xor3, xor_cnf] },
  { unfold tseitin_xor3, simp [h] }
end

-- Big theorem
-- Modify to state that the greatest element of ls is its length
-- TODO max var operates on clauses, but this is a list literal, clean up types later
theorem tseitin_xor3_correct (α : assignment) : ∀ {ls : list literal}, ∀ {n : nat},
  (map var ls).nodup → n = max_var ls → cnf.eval α (xor_cnf ls) = cnf.eval α (tseitin_xor3 ls n)
| []   n := by { simp [xor_cnf, tseitin_xor3] }
| [l]  n := begin
  intros _ hmax,
  have hlen : length [l] = 1, simp [length],
  rw tseitin_xor3_base_case n (eq.trans_le hlen (nat.one_le_bit1 1))
end
| (l₁ :: [l₂]) n := begin
  intros _ _,
  have hlen : length (l₁ :: [l₂]) = 2, simp [length],
  rw tseitin_xor3_base_case n (eq.trans_le hlen (nat.le_succ 2))
end
| (l₁ :: l₂ :: [l₃]) n := begin
  intros _ _,
  have hlen : length (l₁ :: l₂ :: [l₃]) = 3, simp [length],
  rw tseitin_xor3_base_case n (eq.symm hlen).ge
end
| (l₁ :: l₂ :: l₃ :: l₄ :: l) n := begin
  intros hnodup hmax,
  have : 3 < 4, from nat.lt.base 3,
  have : 3 < (length l) + 4, from nat.lt_add_left 3 4 (length l) this,
  have hlen : (length l) + 1 + 1 + 1 + 1 > 3, simp [length, this],
  have hlen2 : ¬((length l) + 1 + 1 + 1 + 1 ≤ 3), from not_le.mpr this,
  unfold tseitin_xor3,
  simp [hlen2],
  have hnodup_original := hnodup,
  rw map_cons at hnodup,
  rw map_cons at hnodup,
  rw map_cons at hnodup,
  have t1 := nodup_of_nodup_cons hnodup,
  have t2 := nodup_of_nodup_cons t1,
  have t3 := nodup_of_nodup_cons t2,

  have : (l₁ :: l₂ :: l₃ :: l₄ :: l) ≠ [], from cons_ne_nil l₁ (l₂ :: l₃ :: l₄ :: l),
  have ngt : n + 1 > n, from lt_add_one n,

  have s1 : max_var (l₂ :: l₃ :: l₄ :: l) ≤ max_var (l₁ :: l₂ :: l₃ :: l₄ :: l), 
    from max_var_le_max_var_cons _ _,
  have s2 : max_var (l₃ :: l₄ :: l) ≤ max_var (l₂ :: l₃ :: l₄ :: l),
    from max_var_le_max_var_cons _ _,
  have s3 : max_var (l₄ :: l) ≤ max_var (l₃ :: l₄ :: l),
    from max_var_le_max_var_cons _ _,
  have s23 : max_var (l₄ :: l) ≤ max_var (l₂ :: l₃ :: l₄ :: l),
    from le_trans s3 s2,
  have s13 : max_var (l₄ :: l) ≤ max_var (l₁ :: l₂ :: l₃ :: l₄ :: l),
    from le_trans s23 s1,
  rw ← hmax at s13,
  have succn_gt : n + 1 > max_var (l₄ :: l), from gt_of_gt_of_ge ngt s13,
  have : (Neg (n + 1)).var = n + 1, simp [var],

  have smallnodup : (map var (l₁ :: l₂ :: l₃ :: [Neg (n + 1)])).nodup,
  { sorry },
  have newnodup : (map var (l₄ :: (l ++ [Pos (n + 1)]))).nodup,
  { sorry },
  have newmaxvar : n + 1 = max_var (l₄ :: (l ++ [Pos (n + 1)])),
  { sorry },


  have ihred := tseitin_xor3_correct newnodup newmaxvar,
  rw cnf.eval_concat,
  rw ← ihred,
  rw xor_cnf_correct α hnodup_original,
  rw xor_cnf_correct α newnodup,
  rw xor_cnf_correct α smallnodup,
  simp [xor_gate.eval_cons, xor_gate.eval_concat],
  rcases bool_by_cases (eval α (Pos (n + 1))) with htt | hff,
  {
    simp [literal.eval] at htt,
    simp [htt, bxor_ff, literal.eval],
  }
end

end tseitin_xor