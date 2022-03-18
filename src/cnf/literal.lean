/-
This file contains the definition of a Boolean literal.
The type of the underlying Boolean variable is polymorphic, such
that Boolean variables may be represented by nats, strings, etc.
 
Authors: Cayden Codel, Jeremy Avigad, Marijn Heule
Carnegie Mellon University
-/

import tactic

universe u

-- Represents the type of the variable stored in the literal
variable {V : Type*}

/-
All propositional formulas are comprised of Boolean literals.
Literals are positive or negative forms of the underlying variable type.
-/
@[derive decidable_eq]
inductive literal (V)
| Pos (v : V) : literal
| Neg (v : V) : literal

/-
Propositional formulas may be evaluated under truth assignments.
Assignments give boolean values to the variables in the formula.
-/
def assignment (V : Type*) := V → bool

namespace literal

open function

/-! # Properties -/

instance [inhabited V] : inhabited (literal V) := ⟨Pos (arbitrary V)⟩

protected def repr [has_repr V] : literal V → string
| (Pos v) := "Pos " ++ (has_repr.repr v)
| (Neg v) := "Neg " ++ (has_repr.repr v)

instance [has_repr V] : has_repr (literal V) := ⟨literal.repr⟩
instance [has_repr V] : has_to_string (literal V) := ⟨literal.repr⟩

/-! # Var -/

/- Extracts the underlying variable of the literal -/
def var : literal V → V
| (Pos v) := v
| (Neg v) := v

theorem var_surjective : surjective (var : literal V → V) :=
assume v, exists.intro (Pos v) (by simp only [var])

theorem ne_of_ne_var {l₁ l₂ : literal V} :
  l₁.var ≠ l₂.var → l₁ ≠ l₂ :=
assume h₁ h₂, h₁ (congr_arg var h₂)

-- Cases on l gives this immediately, so a kind of shorthand
theorem pos_or_neg_of_var_eq_nat {l : literal V} {v : V} :
  l.var = v → l = (Pos v) ∨ l = (Neg v) :=
begin
  cases l,
  { simp only [var], exact or.intro_left false },
  { simp only [var], exact or.intro_right false }
end

/-! # Evaluation -/

/-
When provided an assignment, literals may be evaluated against
that assignment. Negated literals flip the truth value of the
underlying variable when evaluated on the assignment.
-/
protected def eval (τ : assignment V) : literal V → bool
| (Pos v) := τ v
| (Neg v) := bnot (τ v)

/-! # Flip -/

/- Flips the parity of the literal from positive to negative and vice versa -/
-- Protected because "flip" exists already as a way to interchange
-- the order of curried arguments
protected def flip : literal V → literal V
| (Pos v) := Neg v
| (Neg v) := Pos v

@[simp] theorem flip_ne [decidable_eq V] (l : literal V) : l.flip ≠ l :=
by cases l; unfold literal.flip; exact dec_trivial

theorem flip_flip (l : literal V) : l.flip.flip = l :=
by cases l; simp only [literal.flip]

theorem flip_var_eq (l : literal V) : l.flip.var = l.var :=
by cases l; simp only [literal.flip, var]

@[simp] theorem flip_injective : 
  injective (literal.flip : literal V → literal V) :=
assume l₁ l₂ h, (flip_flip l₂) ▸ ((flip_flip l₁) ▸ (congr_arg literal.flip h))

theorem flip_inj {l₁ l₂ : literal V} : l₁.flip = l₂.flip ↔ l₁ = l₂ :=
flip_injective.eq_iff

@[simp] theorem flip_surjective : 
  surjective (literal.flip : literal V → literal V) :=
assume l, exists.intro l.flip (flip_flip l)

@[simp] theorem flip_bijective : 
  bijective (literal.flip : literal V → literal V) :=
⟨flip_injective, flip_surjective⟩

theorem exists_flip_eq (l₁ : literal V) : ∃ (l₂ : literal V), l₂.flip = l₁ :=
begin
  use l₁.flip,
  rw flip_flip
end

-- Various lemmas on how var and flip interact

theorem var_eq_iff_eq_or_flip_eq {l₁ l₂ : literal V} : 
  l₁.var = l₂.var ↔ l₁ = l₂ ∨ l₁.flip = l₂ :=
begin
  split,
  { cases l₁; { cases l₂; simp [literal.flip, var] }},
  { intro h, cases h,
    { exact congr_arg var h },
    { exact congr_arg var h ▸ (flip_var_eq l₁).symm } }
end

theorem flip_eq_iff_eq_flip {l₁ l₂ : literal V} : 
  l₁.flip = l₂ ↔ l₁ = l₂.flip :=
⟨λ h, congr_arg literal.flip h ▸ (flip_flip l₁).symm, 
 λ h, (congr_arg literal.flip h).symm ▸ flip_flip l₂⟩

theorem flip_ne_iff_ne_flip {l₁ l₂ : literal V} :
  l₁.flip ≠ l₂ ↔ l₁ ≠ l₂.flip :=
begin
  split;
  { contrapose,
    simp [flip_eq_iff_eq_flip] },
end

theorem flip_eq_of_ne_of_var_eq {l₁ l₂ : literal V} :
  l₁ ≠ l₂ → l₁.var = l₂.var → l₁.flip = l₂ :=
begin
  intros h₁ h₂,
  cases var_eq_iff_eq_or_flip_eq.mp h₂,
  { contradiction },
  { exact h }
end

theorem eq_of_flip_ne_of_var_eq {l₁ l₂ : literal V} :
  l₁.flip ≠ l₂ → l₁.var = l₂.var → l₁ = l₂ :=
begin
  intros h₁ h₂,
  cases var_eq_iff_eq_or_flip_eq.mp h₂,
  { exact h },
  { contradiction }
end

/-! # Flip evaluation -/

-- When a literal is flipped, its truth assignment is negated
theorem eval_flip (τ : assignment V) (l : literal V) : 
  l.flip.eval τ = bnot (l.eval τ) :=
by cases l; simp only [literal.flip, literal.eval, bnot_bnot]

-- A slight modification where the negation is the flipped literal
theorem eval_flip2 (τ : assignment V) (l : literal V) :
  l.eval τ = bnot (l.flip.eval τ) :=
by cases l; simp only [literal.flip, literal.eval, bnot_bnot]

theorem eval_flip_of_eval {τ : assignment V} {l : literal V} {b : bool} :
  l.eval τ = b → l.flip.eval τ = bnot b :=
assume h, congr_arg bnot h ▸ eval_flip τ l

theorem eval_of_eval_flip {τ : assignment V} {l : literal V} {b : bool} :
  literal.eval τ l.flip = b → literal.eval τ l = bnot b :=
assume h, congr_arg bnot h ▸ eval_flip2 τ l

/-! # Positives and negatives -/

protected def is_pos : literal V → Prop
| (Pos _) := true
| (Neg _) := false

protected def is_neg : literal V → Prop
| (Pos _) := false
| (Neg _) := true

-- Must be protected because of decidable.is_true
protected def is_true (τ : assignment V) (l : literal V) : Prop := 
literal.eval τ l = tt

protected def is_false (τ : assignment V) (l : literal V) : Prop :=
literal.eval τ l = ff

-- is_pos, etc. are decidable
instance : decidable_pred (literal.is_pos : literal V → Prop) :=
begin
  intro l, cases l,
  { unfold literal.is_pos, exact decidable.true },
  { unfold literal.is_pos, exact decidable.false }
end

instance : decidable_pred (literal.is_neg : literal V → Prop) :=
begin
  intro l, cases l,
  { unfold literal.is_neg, exact decidable.false },
  { unfold literal.is_neg, exact decidable.true }
end

instance (τ : assignment V) : decidable_pred (literal.is_true τ) :=
begin
  intro l,
  cases h : literal.eval τ l;
  { unfold literal.is_true, rw h, exact eq.decidable _ _ }
end

instance (τ : assignment V) : decidable_pred (literal.is_false τ) :=
begin
  intro l,
  cases h : literal.eval τ l;
  { unfold literal.is_false, rw h, exact eq.decidable _ _ }
end

-- A literal can never be both positive and negative
theorem is_pos_ne_is_neg (l : literal V) :
  literal.is_pos l ≠ literal.is_neg l :=
by cases l; simp [literal.is_pos, literal.is_neg]

-- A literal can never be both true and false under the same assignment
-- NOTE: A strange proof, can probably be simplified
theorem is_true_ne_is_false [inhabited V] (τ : assignment V) :
  (literal.is_true τ) ≠ (literal.is_false τ) :=
begin
  intro h,
  have v := arbitrary (literal V),
  have := congr_arg (λ (f : literal V → Prop), f v) h,
  cases he : literal.eval τ v;
  { simp [literal.is_true, literal.is_false, he] at this, assumption }
end

end literal