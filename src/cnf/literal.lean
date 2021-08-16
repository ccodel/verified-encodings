/-

  This file contains the definition of a Boolean literal.#check
  
  Authors: Cayden Codel, Jeremy Avigad, Marijn Heule
  Carnegie Mellon University

-/

import init.data.nat

/- 
  All propositional formulas are comprised of Boolean variables.
  Here, we represent variables as natural numbers, which may then be evaluated
  with an appropriate assignment of boolean values to those variables.

  Literals are positive and negative instances of those variables.
-/
inductive literal : Type
  | Pos : nat → literal
  | Neg : nat → literal

/- Assignments give boolean values to the variables -/
def assignment := nat → bool

namespace literal

/- Instance properties -/
instance : inhabited literal := ⟨Pos 0⟩

instance has_decidable_eq : decidable_eq literal
  | (Pos n) (Pos m) :=
    match nat.decidable_eq n m with
      | is_true hnm   := is_true (hnm ▸ eq.refl (Pos n))
      | is_false hneq := is_false (λ h, literal.no_confusion h (λ habs, absurd habs hneq))
    end
  | (Pos _) (Neg _) := is_false (λ h, literal.no_confusion h)
  | (Neg _) (Pos _) := is_false (λ h, literal.no_confusion h)
  | (Neg n) (Neg m) :=
    match nat.decidable_eq n m with
      | is_true hnm   := is_true (hnm ▸ eq.refl (Neg n))
      | is_false hneq := is_false (λ h, literal.no_confusion h (λ habs, absurd habs hneq))
    end

/- Extracts the natural number boolean variable of the literal -/
def var : literal → nat
  | (Pos n) := n
  | (Neg n) := n

/- Negated literals receive the opposite boolean value as the variable -/
def eval (α : assignment) : literal → bool
  | (Pos n) := α n
  | (Neg n) := bnot (α n)

/- Flips the parity of the literal from positive to negative and vice versa -/
def flip : literal → literal
  | (Pos n) := Neg n
  | (Neg n) := Pos n

lemma eval_flip {α : assignment} : ∀ (l : literal), eval α l = bnot (eval α l.flip)
| (Pos n) := by simp [flip, eval]
| (Neg n) := by simp [flip, eval]

lemma eval_flip_flip {α : assignment} : ∀ (l : literal), eval α l = eval α l.flip.flip
| (Pos n) := by simp [flip]
| (Neg n) := by simp [flip]

/- Sets the literal to the positive form -/
def set_pos : literal → literal
  | (Pos n) := Pos n
  | (Neg n) := Pos n

/- Sets the literal to the negative form -/
def set_neg : literal → literal
  | (Pos n) := Neg n
  | (Neg n) := Neg n

/- Returns tt if the literal is positive, ff otherwise -/
def is_pos : literal → bool
  | (Pos _) := tt
  | (Neg _) := ff

/- Returns tt if the literal is negative, ff otherwise -/
def is_neg : literal → bool
  | (Pos _) := ff
  | (Neg _) := tt

-- This seems like a lot of casing... can this be generalized?

@[simp] lemma ne_pos_neg_of_nat {n : nat} : Pos n ≠ Neg n := dec_trivial

@[simp] lemma ne_nat_of_ne_pos {n m : nat} (h : Pos n ≠ Pos m) : n ≠ m :=
begin
  intro heq,
  exact absurd (congr_arg Pos heq) h,
end

@[simp] lemma ne_nat_of_ne_neg {n m : nat} (h : Neg n ≠ Neg m) : n ≠ m :=
begin
  intro heq,
  exact absurd (congr_arg Neg heq) h,
end

@[simp] theorem ne_lit_of_ne_nat {n m : nat} (h : n ≠ m) : Pos n ≠ Neg m := dec_trivial

@[simp] theorem ne_lit_of_nat {n m : nat} : Pos n ≠ Neg m :=
begin
  cases classical.em (n = m) with he hne,
  { rw he, exact ne_pos_neg_of_nat},
  exact ne_lit_of_ne_nat hne,
end

@[simp] theorem ne_pos_of_ne_nat {n m : nat} (h : n ≠ m) : Pos n ≠ Pos m :=
begin
  intro hp,
  exact absurd (congr_arg var hp) h,
end

@[simp] theorem ne_neg_of_ne_nat {n m : nat} (h : n ≠ m) : Neg n ≠ Neg m :=
begin
  intro hp,
  exact absurd (congr_arg var hp) h,
end

end literal