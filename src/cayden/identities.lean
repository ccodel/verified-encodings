/-
  Proving some useful identities in propositional logic
-/

import data.list
import data.finset

open classical

theorem resolution_single (p q r : Prop) : (p ∨ q) ∧ (¬p ∨ r) → q ∨ r :=
begin
  intro h,
  cases h with hpq hpr,
  cases classical.em p,
  cases hpr with hnp hr,

  exfalso,
  exact hnp h,

  exact or.inr hr,

  cases hpq with hp hq,
  exfalso,
  exact h hp,

  exact or.intro_left _ hq,
end

variable α : Prop
#reduce (sizeof α)
#reduce (finset.sizeof Prop {α})
#print finset.sizeof

theorem erase_smaller (s : finset Prop) (a : Prop) (h : a ∈ s) 
  : finset.sizeof Prop (s.erase a) < finset.sizeof Prop s :=
begin
  have k : (s.erase a) ⊂ s, from finset.erase_ssubset h,
  have j : finset.sizeof Prop (s.erase a) = finset.sizeof Prop (s.erase a), from rfl,
  have a_geq: sizeof a ≥ 0, simp, -- what could the reason be? tactic?
  have a_in : a ∈ {a}, from finset.mem_singleton_self a,
  have single_g : sizeof a < finset.sizeof Prop {a}, from finset.sizeof_lt_sizeof_of_mem a_in,
  have singleton_g : 0 < finset.sizeof Prop {a}, from pos_of_gt single_g,
  sorry
end

-- Now let's explore the definition of clauses as finite lists (of props)
def clause := list Prop

def clause_as_list_to_prop : list Prop → Prop
 | []        := ff
 | (x :: xs) := x ∨ (clause_as_list_to_prop xs)

def clause_as_set_to_prop : finset Prop → Prop
| s := 
  if ∃a: Prop, a ∈ s then ∃a ∈ s,
    have finset.sizeof Prop (s.erase a) < finset.sizeof Prop s, from erase_smaller s a H,
    a ∨ (clause_as_set_to_prop (s.erase a))
  else ff

-- TODO: Why : clause not work, but list Prop does?
theorem resolution_clause_as_list (c₁ c₂ : list Prop) (p : Prop) : (p ∈ c₁) ∧ ((¬p) ∈ c₂) → 
  ((clause_as_list_to_prop c₁ ∧ clause_as_list_to_prop c₂) → clause_as_list_to_prop (c₁.append c₂)) :=
begin
  intro hpp,
  cases hpp with hp hnp,
  intro hcc,
  cases hcc with hc1 hc2,
  sorry
end

--theorem resolution_clause_as_set := sorry

-- Now we prove that if we have a list of lists and partition them according to containing p, we can resolve

-- Definition of XOR in logic.lean
-- def xor (a b : Prop) := (a ∧ ¬ b) ∨ (b ∧ ¬ a)

-- Define shorthand for XOR
notation a ⊕ b := xor a b

-- Essentially a proof of de Morgan's laws
lemma xor_as_cnf (a b : Prop) : a ⊕ b ↔ (a ∨ b) ∧ (¬a ∨ ¬b) :=
begin
  split,
  intro h,
  have j : (a ∧ ¬b) ∨ (b ∧ ¬ a), from h,
  cases j with anb bna,
  cases anb with ha hb,
  exact and.intro (or.intro_left _ ha) (or.intro_right _ hb),

  cases bna with hb ha,
  exact and.intro (or.intro_right _ hb) (or.intro_left _ ha),

  intro h,
  cases h with hab hnn,
  cases classical.em a,
  cases classical.em b,
  exfalso,
  cases hnn with han hbn,
  exact han h,
  exact hbn h_1,
  exact or.intro_left _ (and.intro h h_1),
  cases classical.em b,
  exact or.intro_right _ (and.intro h_1 h),
  cases hab with ha hb,
  exfalso,
  exact h ha,
  exfalso,
  exact h_1 hb,
end

-- Now let's try to define XOR for more variables
-- Assumes the Props as arguments are atoms

-- For the XOR gate, the pos versus neg for instantiating isn't really useful
-- as the functions ignore pos/neg and treat all vars as being pos
-- Theoretically, this isn't a problem, as we can just negate all vars until it works
inductive literal : Type
  | Pos : nat → literal
  | Neg : nat → literal

def nat_from_literal : literal → nat 
  | (literal.Pos n) := n
  | (literal.Neg n) := n

--def cnf_clause := list literal
--def cnf := list cnf_clause

--def xor_gate := list literal

namespace xor_gate

def evaluate_xor_helper (α : nat → bool) : list literal → nat → nat
  | [] n                   := n
  | (literal.Pos p :: r) n := bool.to_nat (α p) + evaluate_xor_helper r n
  | (literal.Neg p :: r) n := bool.to_nat (bnot (α p))

-- well-founded goes away if xor_gate becomes list literal
def evaluate_xor (α : nat → bool) : list literal → bool
  | []                    := false
  | (literal.Pos p :: r)  := bxor (α p) (evaluate_xor r)
  | (literal.Neg p :: r)  := bxor (bnot (α p)) (evaluate_xor r)

-- The two branches are literally the same - way to reduce down to one?
-- Way to get prod.mk out of the expression?
def explode_with_negated_count : list literal → list (list literal × nat)
  | []                   := [([], 0)]
  | (literal.Pos p :: r) := 
    let 
      e : list (list literal × nat) := explode_with_negated_count r,
      l1 := list.map (λx, let (l, c) := x in prod.mk (literal.Pos p :: l) (c :  nat)) e,
      l2 := list.map (λx, let (l, c) := x in prod.mk (literal.Neg p :: l) (c + 1)) e
    in 
      list.append l1 l2
  | (literal.Neg p :: r) :=
    let 
      e : list (list literal × nat) := explode_with_negated_count r,
      l1 := list.map (λx, let (l, c) := x in prod.mk (literal.Pos p :: l) (c :  nat)) e,
      l2 := list.map (λx, let (l, c) := x in prod.mk (literal.Neg p :: l) (c + 1)) e
    in 
      list.append l1 l2

def xor_to_cnf : list literal → list (list literal)
  | []                   := [[]]
  | [literal.Pos p]      := [[literal.Pos p]]
  | [literal.Neg p]      := [[literal.Neg p]]
  | (literal.Pos p :: r) :=
    let
      rx := explode_with_negated_count r
    in
      list.map (λx, let (l, (c : nat)) := x in cond (c % 2 = 0) (literal.Pos p :: l) (literal.Neg p :: l)) rx
  | (literal.Neg p :: r) := 
    let
      rx := explode_with_negated_count r
    in
      list.map (λx, let (l, (c : nat)) := x in cond (c % 2 = 0) (literal.Pos p :: l) (literal.Neg p :: l)) rx

end xor_gate

namespace cnf

def evaluate_clause (α : nat → bool) : list literal → bool
  | []                   := false
  | (literal.Pos p :: r) := cond (α p) true (evaluate_clause r)
  | (literal.Neg p :: r) := cond (α p) (evaluate_clause r) true


def evaluate_cnf (α : nat → bool) : list (list literal) → bool
  | []                 := true
  | (l :: ls)          := cond (cnf.evaluate_clause α l) (evaluate_cnf ls) false

end cnf

def g1 : list literal := [literal.Pos 1, literal.Pos 2]
def g2 : list literal := [literal.Pos 1, literal.Pos 2, literal.Pos 3]
def g3 : list literal := [literal.Pos 1, literal.Pos 2, literal.Pos 3, literal.Pos 4]

def c1 : list (list literal) := xor_gate.xor_to_cnf g1
def c2 : list (list literal) := xor_gate.xor_to_cnf g2
def c3 : list (list literal) := xor_gate.xor_to_cnf g3

#reduce c1
#reduce c2
#reduce c3

def a1 : nat → bool
  | 1 := true
  | 2 := true
  | _ := false

def a2 : nat → bool
  | 1 := true
  | 2 := false
  | 3 := false
  | _ := false

def a3 : nat → bool
  | 1 := false
  | 2 := false
  | 3 := true
  | 4 := true
  | _ := false

#reduce cnf.evaluate_cnf a1 c1
#reduce cnf.evaluate_cnf a2 c2
#reduce cnf.evaluate_cnf a3 c3

theorem alternate (g : list literal) (l : literal) (α : nat → bool) :
  cnf.evaluate_cnf α (xor_gate.xor_to_cnf (l :: g)) = bxor (α l) (cnf.evaluate_cnf α (xor_gate.xor_to_cnf g)) :=
begin
  induction g,
  have : xor_gate.xor_to_cnf list.nil = [[]], from rfl,
  rw this,

end

-- Now to prove that both encodings are correct
theorem xor_to_cnf_valid (g : list literal) : ∀(α : nat → bool), xor_gate.evaluate_xor α g = cnf.evaluate_cnf α (xor_gate.xor_to_cnf g) :=
begin
  intro α,
  induction g,
  exact rfl, -- By unrolling of functions? How does lean compute this?

  -- Inductive case  
  cases g_hd with pos_n neg_n,
    have : bxor (α pos_n) (xor_gate.evaluate_xor α g_tl) = xor_gate.evaluate_xor α (literal.Pos pos_n :: g_tl), from rfl,
    rw ← this,
    sorry,

    --have xor_add : (α pos_n) ⊕ (xor_gate.evaluate_xor α g_tl) = xor_gate.evaluate_xor α (litera) 
    /-
    -- Positive literal case
    cases (α pos_n),
      -- Positive literal returns false
    -/




end