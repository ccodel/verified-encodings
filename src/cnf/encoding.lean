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
def encodes (f : list bool → bool) (F : cnf V) (s : list V) :=
  ∀ τ, (f (s.map τ) = tt ↔ ∃ σ, F.eval σ = tt ∧ (τ ≡s.to_finset≡ σ))

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
begin
  intros h₁ h₂ τ,
  split,
  { intro h,
    exact (h₂ τ).mp ((h₁ τ).mp h) },
  { intro h,
    exact (h₁ τ).mpr ((h₂ τ).mpr h) }
end

theorem encodes_of_encodes_of_sequiv {f : list bool → bool} {F₁ F₂ : cnf V} (s : list V) :
  encodes f F₁ s → sequiv F₁ F₂ s.to_finset → encodes f F₂ s :=
begin
  intros h₁ h₂ τ,
  split,
  { intro hf,
    exact (h₂ τ).mp ((h₁ τ).mp hf) },
  { intro h,
    exact (h₁ τ).mpr ((h₂ τ).mpr h) }
end

end encoding