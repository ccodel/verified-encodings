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
variables {V : Type*} [decidable_eq V] [inhabited V]

open literal
open clause
open list
open function

/- Sometimes, it is necessary to take a list of variables and produce a list
   of all possible positive and negative forms of those variables, maintaining
   the order of the original list. We call this operation, "exploding." -/

namespace explode

variables {v : V} {l : list V} {c : clause V}

/-! # Explode -/

def explode : list V → list (clause V)
| []        := [[]]
| (v :: l) := (explode l).map (cons (Pos v)) ++ (explode l).map (cons (Neg v))

@[simp] theorem explode_nil : explode ([] : list V) = [[]] := rfl

@[simp] theorem explode_singleton (v : V) : explode [v] = [[Pos v], [Neg v]] :=
by refl

theorem length_explode (l : list V) : length (explode l) = 2^(length l) :=
begin
  induction l with v vs ih,
  { refl },
  { simp only [explode, length_cons, length_append, 
      length_map, pow_succ, two_mul, ih] }
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

theorem mem_of_mem_explode_of_mem_vars : 
  c ∈ explode l → v ∈ c.vars → v ∈ l :=
begin
  induction l with v vs ih generalizing c,
  { rw [explode_nil, mem_singleton],
    rintros rfl hv, 
    rw clause.vars_nil at hv,
    exact absurd hv (finset.not_mem_empty _) },
  { simp only [explode, mem_append, mem_map],
    rintros (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩);
    { intros hv,
      unfold clause.vars at hv,
      rw finset.mem_union at hv,
      rw mem_cons_iff,
      rcases hv with hv | hv,
      { unfold var at hv,
        rw finset.mem_singleton at hv,
        exact or.inl hv },
      { exact or.inr (ih ha hv) } } }
end

theorem mem_vars_of_mem_explode_of_mem :
  c ∈ explode l → v ∈ l → v ∈ c.vars :=
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

-- Corollaries of the above
theorem not_mem_vars_of_mem_explode_of_not_mem :
  c ∈ explode l → v ∉ l → v ∉ c.vars :=
begin
  intro h,
  contrapose,
  simp only [not_not],
  exact mem_of_mem_explode_of_mem_vars h
end

theorem not_mem_of_mem_explode_of_not_mem_vars :
  c ∈ explode l → v ∉ c.vars → v ∉ l :=
begin
  intro h,
  contrapose,
  simp only [not_not],
  exact mem_vars_of_mem_explode_of_mem h
end

theorem pos_or_neg_of_mem_explode_of_mem :
  c ∈ explode l → v ∈ l → Pos v ∈ c ∨ Neg v ∈ c :=
assume h hv, mem_vars_iff_pos_or_neg_mem_clause.mp 
  (mem_vars_of_mem_explode_of_mem h hv)

theorem pos_and_neg_not_mem_of_mem_explode_of_not_mem :
  c ∈ explode l → v ∉ l → Pos v ∉ c ∧ Neg v ∉ c :=
begin
  intro h,
  contrapose,
  rw not_and_distrib,
  simp only [not_not],
  intro hv,
  exact mem_of_mem_explode_of_mem_vars h 
    (mem_vars_iff_pos_or_neg_mem_clause.mpr hv)
end

-- A theorems concerning the variables of input
-- If explode changes type to (fin)set, remove/update theorem
theorem map_var_eq_iff_mem_explode : c.map var = l ↔ c ∈ explode l :=
begin
  split,
  { induction l with v vs ih generalizing c,
    { simp only [explode_nil, imp_self, map_eq_nil, mem_singleton] },
    { intro h,
      rcases exists_cons_of_map_cons h with ⟨l, ls, rfl, hl, hls⟩,
      rcases pos_or_neg_of_var_eq_nat hl with rfl | rfl,
      { simp [explode], left, use [ls, ih hls] },
      { simp [explode], right, use [ls, ih hls] } } },
  { induction l with v vs ih generalizing c,
    { simp only [explode_nil, imp_self, map_eq_nil, mem_singleton] },
    { simp only [explode, mem_map, mem_append],
      rintros (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩);
      { simp only [ih ha, var, map, eq_self_iff_true, and_self] } } }
end

/-! # nodup properties of explode -/
-- Note: These are not necessary if nodup becomes a (fin)set

theorem explode_nodup (l : list V) : nodup (explode l) :=
begin
  induction l with v vs ih,
  { rw explode_nil, exact nodup_singleton nil },
  { simp only [explode, nodup_cons, nodup_append],
    simp only [nodup_map (cons_injective) ih, true_and],
    intros x hxp hxn,
    rcases mem_map.mp hxp with ⟨c, _, hcx⟩,
    rcases mem_map.mp hxn with ⟨d, _, rfl⟩,
    have := (head_eq_of_cons_eq hcx).symm,
    contradiction }
end

-- TODO Use simp to reduce?
theorem nodup_of_nodup_of_mem (h : nodup l) : c ∈ explode l → nodup c :=
begin
  induction l with n ns ih generalizing c,
  { rw [explode_nil, mem_singleton], rintro rfl, exact nodup_nil },
  { intro hc,
    simp only [explode, mem_append, mem_map] at hc,
    rcases hc with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩,
    { rw nodup_cons,
      have := not_mem_of_nodup_cons h,
      have := pos_and_neg_not_mem_of_mem_explode_of_not_mem ha this,
      exact ⟨this.1, ih (nodup_of_nodup_cons h) ha⟩ },
    { rw nodup_cons,
      have := not_mem_of_nodup_cons h,
      have := pos_and_neg_not_mem_of_mem_explode_of_not_mem ha this,
      exact ⟨this.2, ih (nodup_of_nodup_cons h) ha⟩ } }
end

theorem xor_pos_neg_mem_clause_of_nodup_of_mem_explode_of_mem (h : nodup l) :
  c ∈ explode l → v ∈ l → xor (Pos v ∈ c) (Neg v ∈ c) :=
begin
  induction l with v vs ih generalizing c,
  { intros _ h, exact absurd h (not_mem_nil _) },
  { simp only [explode, mem_append, mem_map],
    rintros (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) hc;
    { rcases eq_or_mem_of_mem_cons hc with (rfl | hv),
      { simp [pos_and_neg_not_mem_of_mem_explode_of_not_mem ha 
            (not_mem_of_nodup_cons h)] },
      { rcases ih (nodup_of_nodup_cons h) ha hv with ⟨hp, hn⟩ | ⟨hp, hn⟩;
        { simp [hp, hn, ne_of_mem_of_not_mem hv (not_mem_of_nodup_cons h)] } } } }
end

end explode