/-

  This file contains the definition of a Boolean literal.
  
  Authors: Cayden Codel, Jeremy Avigad, Marijn Heule
  Carnegie Mellon University

-/

import init.data.nat
import init.logic
import logic.function.basic
import data.list.basic

/- 
  All propositional formulas are comprised of Boolean variables.
  Here, we represent variables as natural numbers, which may then be evaluated
  with an appropriate assignment of boolean values to those variables.

  Literals are positive and negative instances of those variables.
-/
@[derive decidable_eq]
inductive literal : Type
| Pos : nat → literal
| Neg : nat → literal

/- Assignments give boolean values to the variables -/
def assignment := nat → bool

namespace literal

open function

/- Instance properties -/
instance : inhabited literal := ⟨Pos 0⟩

/- Extracts the natural number boolean variable of the literal -/
def var : literal → nat
| (Pos n) := n
| (Neg n) := n

/- Negated literals receive the opposite boolean value as the variable -/
protected def eval (α : assignment) : literal → bool
| (Pos n) := α n
| (Neg n) := bnot (α n)

/-! # Flip -/

/- Flips the parity of the literal from positive to negative and vice versa -/
def flip : literal → literal
| (Pos v) := Neg v
| (Neg v) := Pos v

theorem eval_flip (α : assignment) (l : literal) : literal.eval α l = bnot (literal.eval α l.flip) :=
by cases l; simp [flip, literal.eval]

theorem eval_flip2 (α : assignment) (l : literal) : literal.eval α l.flip = bnot (literal.eval α l) :=
by cases l; simp [flip, literal.eval]

theorem eval_flip_of_eval {α : assignment} {l : literal} {b : bool} :
  literal.eval α l = b → literal.eval α l.flip = !b :=
assume h, by { rw eval_flip at h, exact congr_arg bnot h ▸ (bnot_bnot _).symm }

@[simp] theorem flip_ne (l : literal) : l.flip ≠ l :=
by cases l; simp [flip]

theorem flip_flip (l : literal) : l.flip.flip = l :=
by cases l; simp [flip]

theorem flip_var_eq (l : literal) : l.flip.var = l.var :=
by cases l; simp [flip, var]

-- TODO I sense a two line proof, but I can't get ▸ to work correctly?
@[simp] theorem flip_injective : injective (flip : literal → literal) :=
begin
  intros l₁ l₂ h,
  have := congr_arg flip h,
  simp [flip_flip] at this,
  assumption
end

theorem flip_inj {l₁ l₂ : literal} : l₁.flip = l₂.flip ↔ l₁ = l₂ :=
flip_injective.eq_iff

@[simp] theorem flip_surjective : surjective (flip : literal → literal) :=
assume l, exists.intro l.flip (flip_flip l)

@[simp] theorem flip_bijective : bijective (flip : literal → literal) :=
⟨flip_injective, flip_surjective⟩

-- TODO way to case two things in the same case statement?
lemma eq_or_flip_eq_of_var_eq {l₁ l₂ : literal} : l₁.var = l₂.var → l₁ = l₂ ∨ l₁.flip = l₂ :=
by cases l₁; { cases l₂; simp [flip, var] }

lemma var_eq_of_eq_or_flip_eq {l₁ l₂ : literal} : l₁ = l₂ ∨ l₁.flip = l₂ → l₁.var = l₂.var :=
assume h, or.elim h
  (assume : l₁ = l₂, congr_arg var this)
  (assume : l₁.flip = l₂, congr_arg var this ▸ (flip_var_eq l₁).symm)

theorem eq_or_flip_eq_iff_var_eq {l₁ l₂ : literal} : l₁.var = l₂.var ↔ l₁ = l₂ ∨ l₁.flip = l₂ :=
⟨eq_or_flip_eq_of_var_eq, var_eq_of_eq_or_flip_eq⟩

theorem flip_eq_iff_eq_flip {l₁ l₂ : literal} : l₁.flip = l₂ ↔ l₁ = l₂.flip :=
⟨λ h, congr_arg flip h ▸ (flip_flip l₁).symm, λ h, (congr_arg flip h).symm ▸ flip_flip l₂⟩

theorem flip_eq_of_ne_of_var_eq {l₁ l₂ : literal} :
  l₁ ≠ l₂ → l₁.var = l₂.var → l₁.flip = l₂ :=
begin
  intros h₁ h₂,
  rcases eq_or_flip_eq_of_var_eq h₂,
  { contradiction },
  { exact h }
end

-- Could be proven in terms of the above theorem but too hard/too many ▸
theorem eq_of_flip_ne_of_var_eq {l₁ l₂ : literal} :
  l₁.var = l₂.var → l₁.flip ≠ l₂ → l₁ = l₂ :=
begin
  intros h₁ h₂,
  rcases eq_or_flip_eq_of_var_eq h₁,
  { exact h },
  { contradiction }
end

/-! # Miscellany -/

def set_pos (l : literal) : literal := Pos (l.var)
def set_neg (l : literal) : literal := Neg (l.var)

def is_pos : literal → bool
| (Pos _) := tt
| (Neg _) := ff

/- Returns tt if the literal is negative, ff otherwise -/
def is_neg : literal → bool
| (Pos _) := ff
| (Neg _) := tt

-- TODO this is essentially useless, as casing on l accomplishes the same thing
theorem pos_or_neg_of_var_eq_nat {l : literal} {n : nat} : l.var = n → l = Pos n ∨ l = Neg n :=
by cases l; simp [var]

end literal