/-

  This file contains the definition of a Boolean literal.
  The type of the underlying Boolean variable is polymorphic, such
  that Boolean variables may be represented by nats, strings, etc.
  
  Authors: Cayden Codel, Jeremy Avigad, Marijn Heule
  Carnegie Mellon University

-/

import logic.function.basic
import tactic

universe u

-- Represents the parametric type of the variable stored in the literal
variables {V : Type u} [decidable_eq V] [inhabited V]

/-
All propositional formulas are comprised of Boolean variables.
To represent that these variables can be negated, we introduce
a literal which is either positive or negative (negated).
-/
@[derive decidable_eq]
inductive literal (V)
| Pos (v : V) : literal
| Neg (v : V) : literal

/- Assignments give boolean values to the variables -/
def assignment (V : Type u) := V → bool

namespace literal

open function

instance : inhabited (literal V) := ⟨Pos (arbitrary V)⟩

/-! # Var -/

/- Extracts the underlying variable of the literal -/
def var : literal V → V
| (Pos v) := v
| (Neg v) := v

theorem var_surjective : surjective (var : literal V → V) :=
assume v, exists.intro (Pos v) (by simp only [var])

/-! # Evaluation -/

protected def eval (α : assignment V) : literal V → bool
| (Pos v) := α v
| (Neg v) := bnot (α v)

/-! # Flip -/

/- Flips the parity of the literal from positive to negative and vice versa -/
def flip : literal V → literal V
| (Pos v) := Neg v
| (Neg v) := Pos v

@[simp] theorem flip_ne (l : literal V) : l.flip ≠ l :=
by cases l; simp [flip]

theorem flip_flip (l : literal V) : l.flip.flip = l :=
by cases l; simp only [flip]

theorem flip_var_eq (l : literal V) : l.flip.var = l.var :=
by cases l; simp only [flip, var]

@[simp] theorem flip_injective : injective (flip : literal V → literal V) :=
assume l₁ l₂ h, (flip_flip l₂) ▸ ((flip_flip l₁) ▸ (congr_arg flip h))

theorem flip_inj {l₁ l₂ : literal V} : l₁.flip = l₂.flip ↔ l₁ = l₂ :=
flip_injective.eq_iff

@[simp] theorem flip_surjective : surjective (flip : literal V → literal V) :=
assume l, exists.intro l.flip (flip_flip l)

@[simp] theorem flip_bijective : bijective (flip : literal V → literal V) :=
⟨flip_injective, flip_surjective⟩

lemma eq_or_flip_eq_of_var_eq {l₁ l₂ : literal V} : 
  l₁.var = l₂.var → l₁ = l₂ ∨ l₁.flip = l₂ :=
by cases l₁; { cases l₂; simp [flip, var] }

lemma var_eq_of_eq_or_flip_eq {l₁ l₂ : literal V} : 
  l₁ = l₂ ∨ l₁.flip = l₂ → l₁.var = l₂.var :=
assume h, or.elim h
  (assume : l₁ = l₂, congr_arg var this)
  (assume : l₁.flip = l₂, congr_arg var this ▸ (flip_var_eq l₁).symm)

theorem eq_or_flip_eq_iff_var_eq {l₁ l₂ : literal V} : 
  l₁.var = l₂.var ↔ l₁ = l₂ ∨ l₁.flip = l₂ :=
⟨eq_or_flip_eq_of_var_eq, var_eq_of_eq_or_flip_eq⟩

theorem flip_eq_iff_eq_flip {l₁ l₂ : literal V} : 
  l₁.flip = l₂ ↔ l₁ = l₂.flip :=
⟨λ h, congr_arg flip h ▸ (flip_flip l₁).symm, λ h, (congr_arg flip h).symm ▸ flip_flip l₂⟩

theorem flip_eq_of_ne_of_var_eq {l₁ l₂ : literal V} :
  l₁ ≠ l₂ → l₁.var = l₂.var → l₁.flip = l₂ :=
begin
  intros h₁ h₂,
  cases eq_or_flip_eq_of_var_eq h₂,
  { contradiction },
  { exact h }
end

theorem eq_of_flip_ne_of_var_eq {l₁ l₂ : literal V} :
  l₁.flip ≠ l₂ → l₁.var = l₂.var → l₁ = l₂ :=
begin
  intros h₁ h₂,
  cases eq_or_flip_eq_of_var_eq h₂,
  { exact h },
  { contradiction }
end

/-! # Flip evaluation -/

theorem eval_flip (α : assignment V) (l : literal V) : 
  literal.eval α l = bnot (literal.eval α l.flip) :=
by cases l; simp only [flip, literal.eval, bnot_bnot]

theorem eval_flip2 (α : assignment V) (l : literal V) : 
  literal.eval α l.flip = bnot (literal.eval α l) :=
by cases l; simp only [flip, literal.eval, bnot_bnot]

theorem eval_flip_of_eval {α : assignment V} {l : literal V} {b : bool} :
  literal.eval α l = b → literal.eval α l.flip = bnot b :=
assume h, by { rw eval_flip at h, exact congr_arg bnot h ▸ (bnot_bnot _).symm }

theorem eval_of_eval_flip {α : assignment V} {l : literal V} {b : bool} :
  literal.eval α l.flip = b → literal.eval α l = bnot b :=
begin
  intro h,
  rw eval_flip at h,
  rw flip_flip l at h,
  exact (bnot_bnot (literal.eval α l)) ▸ congr_arg bnot h,
end

/-! # Miscellany -/

def set_pos (l : literal V) : literal V := Pos (l.var)
def set_neg (l : literal V) : literal V := Neg (l.var)

def is_pos : literal V → Prop
| (Pos _) := true
| (Neg _) := false

def is_neg : literal V → Prop
| (Pos _) := false
| (Neg _) := true

def is_true (α : assignment V) (l : literal V) : Prop := literal.eval α l = tt

def is_false (α : assignment V) (l : literal V) : Prop := literal.eval α l = ff

instance : decidable_pred (is_pos : literal V → Prop) :=
begin
  intro l,
  cases l,
  { unfold is_pos, exact decidable.true },
  { unfold is_pos, exact decidable.false }
end

instance : decidable_pred (is_neg : literal V → Prop) :=
begin
  intro l,
  cases l,
  { unfold is_neg, exact decidable.false },
  { unfold is_neg, exact decidable.true }
end

instance (α : assignment V) : decidable_pred (is_true α) :=
begin
  intro l,
  cases h : literal.eval α l,
  { unfold is_true, simp [h], exact decidable.false },
  { unfold is_true, simp [h], exact decidable.true }
end

instance (α : assignment V) : decidable_pred (is_false α) :=
begin
  intro l,
  cases h : literal.eval α l,
  { unfold is_false, simp [h], exact decidable.true },
  { unfold is_false, simp [h], exact decidable.false }
end

-- What a strange proof
theorem is_false_eq_neg_is_true [inhabited V] (α : assignment V) : 
  ¬(is_true α) = is_false α :=
begin
  intro h,
  have v := arbitrary (literal V),
  have := congr_arg (λ (f : literal V → Prop), f v) h,
  cases he : literal.eval α v;
  { simp [is_true, is_false, he] at this, assumption }
end

-- More straightforward way?
theorem is_true_eq_neg_is_false [inhabited V] (α : assignment V) :
  ¬(is_false α) = is_true α :=
(push_neg.not_eq (is_false α) (is_true α)).mpr (ne.symm (is_false_eq_neg_is_true α))

theorem bnot_is_neg_of_is_pos {l : literal V} {b : bool} :
  is_pos l = b → is_neg l = bnot b :=
by cases l; simp [is_pos, is_neg]

theorem bnot_is_pos_of_is_neg {l : literal V} {b : bool} :
  is_neg l = b → is_pos l = bnot b :=
by cases l; simp [is_pos, is_neg]

@[simp] theorem pos_ne_neg (v : V) : Pos v ≠ Neg v :=
by simp

theorem ne_of_ne_var {l₁ l₂ : literal V} : l₁.var ≠ l₂.var → l₁ ≠ l₂ :=
begin
  contrapose,
  simp,
  intro h,
  rw h
end

theorem pos_or_neg_of_var_eq_nat {l : literal V} {v : V} :
  l.var = v → l = (Pos v) ∨ l = (Neg v) :=
by cases l; simp [var]

end literal