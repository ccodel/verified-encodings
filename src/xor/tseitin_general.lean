/-
This file proves that the Tseitin encoding holds for general propositional formulas.

Authors: Cayden Codel, Jeremy Avigad, Marijn Heule
Carnegie Mellon University
-/

import cnf.assignment
import cnf.literal
import cnf.clause
import cnf.cnf

-- First try : a formula is a literal
-- Or it is two formulas joined by a connector,
--   the connector is a formula of left and right halves to bool on eval
inductive form : Type
| lit : literal → form
| conn : form → form → (bool → bool → bool) → form

namespace form 

open literal
open assignment
open clause
open cnf

protected def eval (α : assignment) (to_cnf : form → cnf) : form → bool
| (lit l) := literal.eval α l
| (conn f₁ f₂ op) := op (cnf.eval α (to_cnf f₁)) (cnf.eval α (to_cnf f₂))

theorem tseitin_thm (α : assignment) (to_cnf : form → cnf) (f₁ f₂ : form) (op : bool → bool → bool) :
  ∃ (α₂ : assignment), eqod α α₂ (cnf.vars (to_cnf f₁) ∪ cnf.vars (to_cnf f₂)) → 
  ∃ (n : nat), n ∉ cnf.vars (to_cnf f₁) ∧ n ∉ cnf.vars (to_cnf f₂) →
    cnf.eval α₂ (to_cnf (conn f₁ f₂ op)) = 
      (band (cnf.eval α (to_cnf (conn f₁ (lit (Neg n)) bxor))) 
            (cnf.eval α (to_cnf (conn (lit (Pos n)) f₂ bxor)))) :=
begin
  have max1 : (max (max_nat (cnf.vars (to_cnf f₁))) (max_nat (cnf.vars (to_cnf f₂)))) + 1 > max_nat (cnf.vars (to_cnf f₁)),
  { have : max_nat (cnf.vars (to_cnf f₁)) ≤ max (max_nat (cnf.vars (to_cnf f₁))) (max_nat (cnf.vars (to_cnf f₂))),
      from le_max_left (max_nat (vars (to_cnf f₁))) (max_nat (vars (to_cnf f₂))),
    exact nat.lt_succ_iff.mpr this },
  have notmem1 := not_mem_of_gt_max_nat max1,

  have max2 : (max (max_nat (cnf.vars (to_cnf f₁))) (max_nat (cnf.vars (to_cnf f₂)))) + 1 > max_nat (cnf.vars (to_cnf f₂)),
  { have : max_nat (cnf.vars (to_cnf f₂)) ≤ max (max_nat (cnf.vars (to_cnf f₁))) (max_nat (cnf.vars (to_cnf f₂))),
      from le_max_right (max_nat (vars (to_cnf f₁))) (max_nat (vars (to_cnf f₂))),
    exact nat.lt_succ_iff.mpr this },
  have notmem2 := not_mem_of_gt_max_nat max2,

  have notmem12 : (max (max_nat (cnf.vars (to_cnf f₁))) (max_nat (cnf.vars (to_cnf f₂)))) + 1 ∉ (cnf.vars (to_cnf f₁)) ∪ (cnf.vars (to_cnf f₂)),
    simp [not_or_distrib, notmem1, notmem2],
  
  have := exists_extended_assignment_of_assignment α notmem12,
  
end

end form