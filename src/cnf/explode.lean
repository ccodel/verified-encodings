/-
This file contains the definition of the "explode" operation, which
creates a "powerset" of literals from a list of variables. Associated
theorems dealing with the contents of explode are also included.

Authors: Cayden Codel, Jeremy Avigad, Marijn Heule
Carnegie Mellon University
-/

import cnf.literal
import cnf.clause
import cnf.cnf

import data.nat.basic
import data.nat.pow

universe u

-- Represents the parametric type of the variable stored in the literal
variables {V : Type*}

open literal clause
open list function

namespace explode

variables {v : V} {l : list V} {c : clause V}

/-! # Explode -/

-- Produces a list of all possible polarities on a list of variables, maintaining order
def explode : list V → list (clause V)
| []        := [[]]
| (v :: l) := (explode l).map (cons (Pos v)) ++ (explode l).map (cons (Neg v))

@[simp] theorem explode_nil : explode ([] : list V) = [[]] := rfl

@[simp] theorem explode_singleton (v : V) : explode [v] = [[Pos v], [Neg v]] := rfl

theorem length_explode (l : list V) : length (explode l) = 2^(length l) :=
begin
  induction l with v vs ih,
  { refl },
  { simp only [explode, length_cons, length_append, length_map, pow_succ, two_mul, ih] }
end

theorem length_explode_pos (l : list V) : length (explode l) > 0 :=
by { rw length_explode, exact pow_pos zero_lt_two _ }

theorem exists_mem_explode (l : list V) : ∃ (c : clause V), c ∈ explode l :=
exists_mem_of_length_pos (length_explode_pos _)

theorem length_eq_of_mem_explode : c ∈ explode l → length c = length l :=
begin
  induction l with v vs ih generalizing c,
  { rw [explode_nil, mem_singleton],
    rintro rfl, refl },
  { simp only [explode, mem_append, mem_map],
    rintros (⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩);
    { simp [ih hc, length_cons] } }
end

theorem cons_mem_explode_cons_of_mem_explode (lit : literal V) : 
  c ∈ explode l → (lit :: c) ∈ explode (lit.var :: l) :=
assume hc, by { cases lit; simp [explode, literal.var, hc] }

variable [decidable_eq V]

theorem mem_of_mem_explode_of_mem_vars : c ∈ explode l → v ∈ c.vars → v ∈ l :=
begin
  induction l with v vs ih generalizing c,
  { rw [explode_nil, mem_singleton],
    rintros rfl hv, 
    rw clause.vars_nil at hv,
    exact absurd hv (finset.not_mem_empty _) },
  { simp only [explode, mem_append, mem_map],
    rintros (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩);
    { rw [clause.vars, finset.mem_union, mem_cons_iff],
      rintros (hv | hv),
      { rw [var, finset.mem_singleton] at hv,
        exact or.inl hv },
      { exact or.inr (ih ha hv) } } }
end

theorem mem_vars_of_mem_explode_of_mem : c ∈ explode l → v ∈ l → v ∈ c.vars :=
begin
  induction l with v vs ih generalizing c,
  { intros _ hv, exact absurd hv (not_mem_nil v) } ,
  { simp only [explode, mem_append, mem_map],
    rintros (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) hv;
    { unfold clause.vars var,
      rcases eq_or_mem_of_mem_cons hv with rfl | hv,
      { exact finset.mem_union.mpr (or.inl (mem_singleton_self _)) },
      { exact finset.mem_union.mpr (or.inr (ih ha hv)) } } }
end

theorem not_mem_vars_of_mem_explode_of_not_mem : c ∈ explode l → v ∉ l → v ∉ c.vars :=
λ h hv, mt (mem_of_mem_explode_of_mem_vars h) hv

theorem not_mem_of_mem_explode_of_not_mem_vars : c ∈ explode l → v ∉ c.vars → v ∉ l :=
λ h hv, mt (mem_vars_of_mem_explode_of_mem h) hv

theorem pos_or_neg_of_mem_explode_of_mem : c ∈ explode l → v ∈ l → Pos v ∈ c ∨ Neg v ∈ c :=
λ h hv, mem_vars_iff_pos_or_neg_mem_clause.mp (mem_vars_of_mem_explode_of_mem h hv)

theorem pos_and_neg_not_mem_of_mem_explode_of_not_mem : c ∈ explode l → v ∉ l → Pos v ∉ c ∧ Neg v ∉ c :=
begin
  intro h,
  contrapose,
  rw not_and_distrib,
  simp only [not_not],
  intro hv,
  exact mem_of_mem_explode_of_mem_vars h 
    (mem_vars_iff_pos_or_neg_mem_clause.mpr hv)
end

-- If the variables in a clause match the input to explode, then it's in explode
theorem map_var_eq_iff_mem_explode : c.map var = l ↔ c ∈ explode l :=
begin
  induction l with v vs ih generalizing c,
  { simp only [map_eq_nil, explode_nil, mem_singleton] },
  { split,
    { intro h,
      rcases exists_cons_of_map_cons h with ⟨l, ls, rfl, hl, hls⟩,
      cases l; simp only [explode, mem_append, mem_map],
      { rw var at hl, subst hl, left, use [ls, ih.mp hls] },
      { rw var at hl, subst hl, right, use [ls, ih.mp hls] } },
    { simp only [explode, mem_map, mem_append],
      rintros (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩);
      { simp only [ih.mpr ha, var, map, eq_self_iff_true, and_self] } } }
end

/-! # nodup properties of explode -/

theorem explode_nodup (l : list V) : nodup (explode l) :=
begin
  induction l with v vs ih,
  { rw explode_nil, exact nodup_singleton nil },
  { simp only [explode, nodup_cons, nodup_append, (nodup_map_iff (cons_injective)).mpr ih, true_and],
    intros x hxp hxn,
    rcases mem_map.mp hxp with ⟨c, _, rfl⟩,
    rcases mem_map.mp hxn with ⟨d, _, h⟩,
    have := head_eq_of_cons_eq h,
    contradiction }
end

theorem nodup_of_nodup_of_mem (h : nodup l) : c ∈ explode l → nodup c :=
begin
  induction l with n ns ih generalizing c,
  { rw [explode_nil, mem_singleton], rintro rfl, exact nodup_nil },
  { simp only [explode, mem_append, mem_map],
    rintro (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩);
    rw nodup_cons;
    have := pos_and_neg_not_mem_of_mem_explode_of_not_mem ha ((nodup_cons.mp h).1),
    { exact ⟨this.1, ih (nodup_cons.mp h).2 ha⟩ },
    { exact ⟨this.2, ih (nodup_cons.mp h).2 ha⟩ } }
end

theorem xor_pos_neg_mem_clause_of_nodup_of_mem_explode_of_mem (h : nodup l) :
  c ∈ explode l → v ∈ l → xor (Pos v ∈ c) (Neg v ∈ c) :=
begin
  induction l with v vs ih generalizing c,
  { intros _ h, exact absurd h (not_mem_nil _) },
  { simp only [explode, mem_append, mem_map],
    rintros (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) hc;
    { rcases eq_or_mem_of_mem_cons hc with (rfl | hv),
      { simp [pos_and_neg_not_mem_of_mem_explode_of_not_mem ha (nodup_cons.mp h).1] },
      { rcases ih (nodup_cons.mp h).2 ha hv with ⟨hp, hn⟩ | ⟨hp, hn⟩;
        { simp [hp, hn, ne_of_mem_of_not_mem hv (nodup_cons.mp h).1] } } } }
end

end explode