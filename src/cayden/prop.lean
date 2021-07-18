import init
import data.bool
--import init.data.bool.basic
--import init.data.bool.lemmas

inductive PropForm : Type
  -- Atoms of propositional formulas
  | T      : PropForm
  | F      : PropForm
  | Var    : nat → PropForm -- Identified by ID number

  -- Basic connectives for propositional formulas
  | Conj   : PropForm → PropForm → PropForm
  | Disj   : PropForm → PropForm → PropForm
  | Neg    : PropForm → PropForm

 -- Other gates 
  | Imp    : PropForm → PropForm → PropForm
  --| Xor    : PropForm → PropForm → PropForm
  --| Nand   : PropForm → PropForm → PropForm
  --| Nor    : PropForm → PropForm → PropForm
  --| NXor   : PropForm → PropForm → PropForm

-- Alternative definitions of different prop forms
inductive NNFPropForm : Type
  | T       : NNFPropForm
  | F       : NNFPropForm
  | Var     : nat → NNFPropForm
  | Conj    : NNFPropForm → NNFPropForm → NNFPropForm
  | Disj    : NNFPropForm → NNFPropForm → NNFPropForm
  | Neg     : NNFPropForm → NNFPropForm

inductive literal : Type
| T   : literal
| F   : literal
| Pos : nat → literal
| Neg : nat → literal

def clause := list literal
def cnf := list clause

namespace PropForm

prefix `x`:100 := PropForm.Var
notation `TT` := PropForm.T
notation `FF` := PropForm.F

--infixr ` ⋀ `:35 := PropForm.Conj -- \And
--infixr ` ⋁ `:30 := PropForm.Disj -- \Or
prefix `!`:100 := PropForm.Neg
infixr ` ~> `:20 := PropForm.Impl
--infixr ` ⊕ ` := PropForm.Xor
--infixr ` !⋀ `:25 := PropForm.Nand
-- Other two...

-- partial in Lean 4 allows you to make any recursive call you want

-- Negation normal form translation function
-- Cases spelled out longhand to prevent well-founded error
def nnf : PropForm → NNFPropForm
  | T                := NNFPropForm.T
  | F                := NNFPropForm.F
  | (Var n)          := NNFPropForm.Var n
  | (Conj p q)       := NNFPropForm.Conj (nnf p) (nnf q)
  | (Disj p q)       := NNFPropForm.Disj (nnf p) (nnf q)

  -- All cases of imp by hand
  | (Imp T q)        := NNFPropForm.Disj (nnf F) (nnf q)
  | (Imp F q)        := NNFPropForm.Disj (nnf T) (nnf q)
  | (Imp (Var n) q)  := NNFPropForm.Disj (NNFPropForm.Neg (NNFPropForm.Var n)) (nnf q)
  | (Imp (Conj p1 p2) q) := NNFPropForm.Disj (NNFPropForm.Disj (nnf (Neg p1)) (nnf (Neg p2))) (nnf q)
  | (Imp (Disj p1 p2) q) := NNFPropForm.Disj (NNFPropForm.Conj (nnf (Neg p1)) (nnf (Neg p2))) (nnf q)
  | (Imp (Neg p) q)      := NNFPropForm.Disj (nnf p) (nnf q)
  | (Imp (Imp p1 p2) q) := NNFPropForm.Disj (NNFPropForm.Conj (nnf p1) (nnf (Neg p2))) (nnf q)
  --| (Imp (Xor p1 p2) q) := Disj (Disj (Conj (nnf p1) (nnf p2)) (Conj (nnf (Neg p1)) (nnf (Neg p2)))) (nnf q)
  --| (Xor p q)        := Conj (Disj (nnf p) (nnf q)) (Disj (nnf (Neg p)) (nnf (Neg q)))

  -- Now for the various Neg cases
  | (Neg T)          := NNFPropForm.F
  | (Neg F)          := NNFPropForm.T
  | (Neg (Var n))    := NNFPropForm.Neg (NNFPropForm.Var n)
  | (Neg (Conj p q)) := NNFPropForm.Disj (nnf (Neg p)) (nnf (Neg q))
  | (Neg (Disj p q)) := NNFPropForm.Conj (nnf (Neg p)) (nnf (Neg q))
  | (Neg (Neg p))    := nnf p
  | (Neg (Imp p q))  := NNFPropForm.Conj (nnf p) (nnf (Neg q))

end PropForm

namespace NNFPropForm

def nnf_to_cnf : NNFPropForm → cnf
  | T           := [[literal.T]]
  | F           := [[literal.F]]
  | (Var n)     := [[literal.Pos n]]
  | (Conj p q)  := list.append (nnf_to_cnf p) (nnf_to_cnf q)

  | (Disj p q)  := nnf_to_cnf p -- TODO

  | (Neg T)     := [[literal.F]]
  | (Neg F)     := [[literal.T]]
  | (Neg (Var n)) := [[literal.Neg n]]
  | (Neg (Conj p q)) := nnf_to_cnf p -- TODO
  | (Neg (Disj p q)) := list.append (nnf_to_cnf (Neg p)) (nnf_to_cnf (Neg q))
  | (Neg (Neg p)) := nnf_to_cnf p

end NNFPropForm

namespace cnf

def clause_evaluate : clause → (nat → bool) → bool
  | [] _ := ff
  | (literal.T :: cs) _ := tt
  | (literal.F :: cs) α := clause_evaluate cs α
  | ((literal.Pos n) :: cs) α :=
      (α n || clause_evaluate cs α)
  | ((literal.Neg n) :: cs) α :=
      (bnot (α n) || clause_evaluate cs α)

def evaluate : cnf → (nat → bool) → bool
| [] _ := tt
| (cl :: cls) α :=
    (clause_evaluate cl α && evaluate cls α)

-- Look into finite sets as a list substitute
  -- Be careful with recursion on sets
def c1 : clause := [literal.Pos 1, literal.Pos 2]
def c2 : clause := [literal.Pos 2, literal.Pos 1]
def f1 : cnf := [[literal.Pos 1, literal.Pos 2]] -- x1 v x2
def f2 : cnf := [[literal.Pos 2, literal.Pos 1]] -- x2 v x1

---set_option trace.simplify true

#print prefix bool

example : (∀ α, evaluate f1 α = evaluate f2 α) :=
  begin
    intro h,
    simp [evaluate, clause_evaluate, f1, f2],
    rw bool.bor_comm,
  end

end cnf

open classical

/-
variables p q : Prop
example (hp : p) (hq : q) : and p q := and.intro hp hq
example (hpq : and p q) : and q p := 
  begin
    cases hpq with hp hq,
    split,
    exact hq,
    exact hp,
  end
  -/

-- Representation of boolean logic?
def domain : set nat := {0, 1}

open bool

example (r s : bool) (p : bool → Prop) : p (r && s) ↔ p (s && r) :=
  begin
    split,
    intro f,
    rw band_comm,
    exact f,

    intro f,
    rw band_comm,
    exact f,
  end

#print prefix list
#print prefix bool

-- Convert prop to bool by equals and substituting connectives
-- by_cases (cases) is an option, too
theorem resolution (p q r : Prop) (hp : p) (hq : q) (hr : r) : (p ∧ q) ∨ (¬p ∧ r) ↔ q ∧ r :=
begin
  split,
  intro hpqr,
  exact and.intro hq hr,

  intro hqr,
  have hpq: p ∧ q, from and.intro hp hq,
  have hpqpr: (p ∧ q) ∨ (¬p ∧ r), from or.intro_left _ hpq,
  exact hpqpr,
end

-- x ⊕ y  ==> (x v y) ^ (!x v !y)
-- x ⊕ y  ==> (x v x v y v y) ^ (!x v !y)