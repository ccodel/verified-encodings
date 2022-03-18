/-
This file sets out definitions of what it means for a CNF formula to encode
a Boolean function. Encodings of non-Boolean functions may require different
definitions.

Authors: Cayden Codel, Marijn Heule, Jeremy Avigad
Carnegie Mellon University
-/

import cnf.literal
import cnf.assignment
import cnf.clause
import cnf.cnf
import basic

universe u

variables {V : Type*} [decidable_eq V] [inhabited V]

namespace encoding

open assignment

/- A CNF formula encodes a Boolean function -/
def encodes (f : list bool → bool) (F : cnf V) (l : list (literal V)) :=
  ∀ τ, (f (l.map (literal.eval τ)) = tt ↔ ∃ σ, F.eval σ = tt ∧ (τ ≡(clause.vars l)≡ σ))

/- Definition of S-equivalence -/
def sequiv (F₁ F₂ : cnf V) (s : finset V) := ∀ τ, 
  ((∃ σ₁, F₁.eval σ₁ = tt ∧ (τ ≡s≡ σ₁)) ↔ (∃ σ₂, F₂.eval σ₂ = tt ∧ (τ ≡s≡ σ₂)))

@[refl] theorem sequiv.refl (F : cnf V) (s : finset V) : sequiv F F s :=
assume _, iff.rfl

@[symm] theorem sequiv.symm {F₁ F₂ : cnf V} {s : finset V} :
  sequiv F₁ F₂ s → sequiv F₂ F₁ s :=
assume h τ, (h τ).symm

@[trans] theorem sequiv.trans {F₁ F₂ F₃ : cnf V} {s : finset V} :
  sequiv F₁ F₂ s → sequiv F₂ F₃ s → sequiv F₁ F₃ s :=
assume h₁ h₂ τ, ⟨λ h, (h₂ τ).mp ((h₁ τ).mp h), λ h, (h₁ τ).mpr ((h₂ τ).mpr h)⟩

theorem encodes_of_encodes_of_sequiv {f : list bool → bool} {F₁ F₂ : cnf V} {l : list (literal V)} :
  encodes f F₁ l → sequiv F₁ F₂ (clause.vars l) → encodes f F₂ l :=
assume h₁ h₂ τ, ⟨λ h, (h₂ τ).mp ((h₁ τ).mp h), λ h, (h₁ τ).mpr ((h₂ τ).mpr h)⟩

end encoding