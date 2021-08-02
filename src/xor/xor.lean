/-

  This file concerns the definition and translation of XOR gates into CNF, and
  proves that this translation is correct.

  Authors: Cayden Codel, Jeremy Avigad, Marijn Heule
  Carnegie Mellon University

-/

import data.bool
import cayden.cnf
import basic

/- Let's define an XOR gate -/
def xor_g := list literal

namespace xor_g

open literal

/- Evaluates the XOR gate under an assignment -/
def eval (α : assignment) (g : xor_g) : bool :=
  g.foldr (λ l, λ b, b ⊕ l.eval α) ff

def to_cnf : xor_g → cnf
  | []        := []
  | [l]       := [[l]]
  | (l :: ls) := list.map (λ r, let (c, p) := r in cond p (l.set_pos :: c) (l.set_neg :: c))) (explode.expl_parity (ls.map (λ x, x.var)))

def evaluate_xor_helper (α : literal → bool) : list literal → nat → nat
  | [] n        := n
  | (l :: ls) n := bool.to_nat (α l) + evaluate_xor_helper ls n

def explode_with_negated_count : list literal → list (list literal × nat)
  | []        := [([], 0)]
  | (l :: ls) :=
    let
      e : list (list literal × nat) := explode_with_negated_count ls,
      l1 := list.map (λx, let (lss, c) := x in prod.mk (literal.Pos (nat_from_literal l) :: lss) (c : nat)) e,
      l2 := list.map (λx, let (lss, c) := x in prod.mk (literal.Neg (nat_from_literal l) :: lss) (c + 1)) e
    in
      list.append l1 l2

def xor_to_cnf : list literal → list (list literal)
  | []        := [[]]
  | [l]       := [[l]]
  | (l :: ls) := 
    let
      ls_ex := explode_with_negated_count ls
    in
      list.map (λx, let (lss, (c : nat)) := x in 
        cond (c % 2 = 0) (literal.Pos (nat_from_literal l) :: lss) (literal.Neg (nat_from_literal l) :: lss)) ls_ex

end xor_g