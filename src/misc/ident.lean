/-
  Proving some useful identities in propositional logic
-/

import data.bool
import data.list
import data.list.basic

-- Define shorthand for XOR
notation a ⊕ b := bxor a b

-- Some trivial, useful theorems
@[simp] theorem bxor_tt_left  : ∀ a, bxor tt a = bnot a := dec_trivial
@[simp] theorem bxor_tt_right : ∀ a, bxor a tt = bnot a := dec_trivial

theorem cond_tt_ff : ∀ a, cond a tt ff = a := dec_trivial
theorem cond_ff_tt : ∀ a, cond a ff tt = bnot a := dec_trivial

inductive literal : Type
  | Pos : nat → literal
  | Neg : nat → literal

def nat_from_literal : literal → nat 
  | (literal.Pos n) := n
  | (literal.Neg n) := n

def explode : list literal → list (list literal)
  | []        := []
  | [l]       := [[literal.Pos (nat_from_literal l)], [literal.Neg (nat_from_literal l)]]
  | (l :: ls) :=
    let 
      e := explode ls
    in
      list.append (list.map (λlss, literal.Pos (nat_from_literal l) :: lss) e) (list.map (λlss, literal.Neg (nat_from_literal l) :: lss) e)


namespace xor_gate

def evaluate_xor_helper (α : literal → bool) : list literal → nat → nat
  | [] n        := n
  | (l :: ls) n := bool.to_nat (α l) + evaluate_xor_helper ls n

def evaluate_xor (α : literal → bool) : list literal → bool
  | []        := ff
  | (l :: ls) := bxor (α l) (evaluate_xor ls)

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

end xor_gate


namespace cnf

def evaluate_clause (α : literal → bool) : list literal → bool
  | []        := ff
  | (l :: ls) := cond (α l) tt (evaluate_clause ls)

def evaluate_cnf (α : literal → bool) : list (list literal) → bool
  | []         := tt
  | ([] :: ls) := ff
  | (l :: ls)  := cond (cnf.evaluate_clause α l) (evaluate_cnf ls) ff

theorem eval_single (α : literal → bool) (ls : list (list literal)) (l : literal) : ls = [[l]] → evaluate_cnf α ls = α l :=
begin
  intro h,
  calc
    evaluate_cnf α ls = evaluate_cnf α [[l]] : by { rw h }
                  ... = cond (evaluate_clause α [l]) (evaluate_cnf α []) ff : rfl
                  ... = cond (evaluate_clause α [l]) tt ff : rfl
                  ... = evaluate_clause α [l] : by { rw cond_tt_ff }
                  ... = cond (α l) tt (evaluate_clause α []) : rfl
                  ... = cond (α l) tt ff : rfl
                  ... = α l : by { rw cond_tt_ff }
end

-- Some theorems about exploding
theorem explode_at_least_two (ls : list literal) : ls ≠ [] → ∃c ∈ (explode ls), ∃d, c ≠ d ∧ d ∈ (explode ls) :=
begin
  intro h,
  induction ls,
  exfalso,
  have k : ([] : list literal) = [], from rfl,
  exact h k,
  cases ls_tl,
  have k : explode [ls_hd] = [[literal.Pos (nat_from_literal ls_hd)], [literal.Neg (nat_from_literal ls_hd)]], from rfl,
  rw k,
  have c := (explode [ls_hd]).head,
  have d := [literal.Pos (nat_from_literal ls_hd)],
  use c,
  split,
  
end

theorem explode_sat (ls : list literal) (α : literal → bool) : ls ≠ [] → ∃c ∈ (explode ls), evaluate_clause α c = tt :=
begin
  intro h,
  induction ls,
  exfalso,
  have k : ([] : list literal) = [], from rfl,
  exact h k,
  cases α ls_hd,


  apply exists.intro,
  use list.empty,
  have k : explode list.nil = list.nil, from rfl,
  rw k,
  
end

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

def a1 : literal → bool
  | (literal.Pos 1) := tt
  | (literal.Neg 1) := ff
  | (literal.Pos 2) := tt
  | (literal.Neg 2) := ff
  | (literal.Pos n) := ff
  | (literal.Neg n) := tt

def a2 : literal → bool
  | (literal.Pos 3) := ff
  | (literal.Neg 3) := tt
  | l               := a1 l

def a3 : literal → bool
  | (literal.Pos 4) := tt
  | (literal.Neg 4) := ff
  | l               := a2 l

#reduce cnf.evaluate_cnf a1 c1
#reduce cnf.evaluate_cnf a2 c2
#reduce cnf.evaluate_cnf a3 c3

/-
theorem alternate (g : list literal) (l : literal) (α : literal → bool) :
  cnf.evaluate_cnf α (xor_gate.xor_to_cnf (l :: g)) = bxor (α l) (cnf.evaluate_cnf α (xor_gate.xor_to_cnf g)) :=
begin
  induction g,
  have h : cnf.evaluate_cnf α (xor_gate.xor_to_cnf []) = ff,
    calc
      cnf.evaluate_cnf α (xor_gate.xor_to_cnf []) = cnf.evaluate_cnf α (xor_gate.xor_to_cnf []) : rfl
                                              ... = cnf.evaluate_cnf α [[]] : rfl
                                              ... = ff : rfl,
  calc
    cnf.evaluate_cnf α (xor_gate.xor_to_cnf [l]) = cnf.evaluate_cnf α (xor_gate.xor_to_cnf [l]) : rfl
                                             ... = cnf.evaluate_cnf α [[l]] : rfl
                                             ... = α l : by { rw cnf.eval_single α [[l]] l, refl }
                                             ... = bxor (α l) ff : by { simp } -- bool.bxor_ff_right
                                             ... = bxor (α l) (cnf.evaluate_cnf α (xor_gate.xor_to_cnf [])) : by { rw h },
  
  calc
    cnf.evaluate_cnf α (xor_gate.xor_to_cnf (l :: g_hd :: g_tl)) = cnf.evaluate_cnf α (xor_gate.xor_to_cnf (l :: g_hd :: g_tl)) : rfl
                                                             ... = 
end
-/

theorem alternate2 [inhabited literal] (g : list literal) (α : literal → bool) : 
  g ≠ [] → cnf.evaluate_cnf α (xor_gate.xor_to_cnf g) = bxor (α g.head) (cnf.evaluate_cnf α (xor_gate.xor_to_cnf g.tail)) :=
begin
  intro h,
  induction g,

  -- Base case
  exfalso,
  exact h rfl,

  -- IH case
  -- Case on length of rest of list
  cases g_tl,
  simp,
  have k : cnf.evaluate_cnf α (xor_gate.xor_to_cnf []) = ff,
    calc
      cnf.evaluate_cnf α (xor_gate.xor_to_cnf []) = cnf.evaluate_cnf α (xor_gate.xor_to_cnf []) : rfl
                                              ... = cnf.evaluate_cnf α [[]] : rfl
                                              ... = ff : rfl,
  rw k,
  simp,
  calc
    cnf.evaluate_cnf α (xor_gate.xor_to_cnf [g_hd]) = cnf.evaluate_cnf α (xor_gate.xor_to_cnf [g_hd]) : rfl
                                                ... = cnf.evaluate_cnf α ([[g_hd]]) : rfl
                                                ... = α g_hd : by { rw cnf.eval_single, refl },                                           
  
  -- Nonempty case
  have k := g_ih (list.cons_ne_nil g_tl_hd g_tl_tl),
  simp,
  simp at k,
  sorry,
  /-
  calc
    cnf.evaluate_cnf α (xor_gate.xor_to_cnf (g_hd :: g_tl_hd :: g_tl_tl)) = cnf.evaluate_cnf α (xor_gate.xor_to_cnf (g_hd :: g_tl_hd :: g_tl_tl)) : rfl
                                                                      ... = cnf.evaluate_cnf 
                                                                      -/
end

-- Now to prove that both encodings are correct
theorem xor_to_cnf_valid (g : list literal) : ∀(α : literal → bool), xor_gate.evaluate_xor α g = cnf.evaluate_cnf α (xor_gate.xor_to_cnf g) :=
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
      -- Positive literal returns ff
    -/




end