/-
This file contains the definition of the "explode" operation, which
creates a "powerset" of literals from a list of variables. Associated
theorems dealing with the contents of explode are also included.

Variables are general.

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
variables {V : Type u} [decidable_eq V] [inhabited V]

open literal
open clause
open list
open function

/- Sometimes, it is necessary to get all possible disjunctive clauses from a set of variables -/
/- For lack of a better name, we call that operation "exploding" -/

-- NOTE: If clauses are switched to sets, explode may also be appropriate as a (fin)set

namespace explode

/-! # Explode -/

def explode : list V → list (clause V)
| []        := [[]]
| (v :: vs) := (explode vs).map (cons (Pos v)) ++ (explode vs).map (cons (Neg v))

@[simp] theorem explode_nil : explode ([] : list V) = [[]] := rfl

@[simp] theorem explode_singleton (v : V) : explode [v] = [[Pos v], [Neg v]] :=
by simp [explode]

theorem length_explode : ∀ (l : list V), length (explode l) = 2^(length l)
| []        := rfl
| (v :: vs) := by simp [explode, length_explode vs, pow_succ, two_mul]

theorem length_explode_pos (l : list V) : length (explode l) > 0 :=
by simp [length_explode]

theorem exists_mem_explode (l : list V) : ∃ (c : clause V), c ∈ explode l :=
exists_mem_of_length_pos (length_explode_pos _)

theorem length_eq_of_mem_explode {l : list V} : 
  ∀ {c : clause V}, c ∈ explode l → length c = length l :=
begin
  induction l with n ns ih, { simp },
  { simp only [explode, mem_append, mem_map],
    rintros c (⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩); simp [length, ih hc] }
end

theorem mem_explode_cons_of_mem_explode_of_lit {l : list V} (lit : literal V) : 
  ∀ {c : clause V}, c ∈ explode l → (lit :: c) ∈ explode (lit.var :: l) :=
assume c hc, by { cases lit; simp [explode, literal.var, hc] }

lemma map_var_eq_of_mem_explode {l : list V} : 
  ∀ {c : clause V}, c ∈ explode l → map var c = l :=
begin
  induction l with n ns ih,
  { simp },
  { simp only [explode, mem_append, mem_map],
    rintros c (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩);
    { simp [var, map_cons, ih ha] } }
end

lemma mem_explode_of_map_var_eq {l : list V} : 
  ∀ {c : clause V}, c.map var = l → c ∈ explode l :=
begin
  induction l with n ns ih,
  { simp },
  { intros c h,
    rcases exists_cons_of_map_cons h with ⟨l, ls, rfl, hl, hls⟩,
    rcases pos_or_neg_of_var_eq_nat hl with rfl | rfl,
    { simp [explode], left, use ls, simp [ih hls] },
    { simp [explode], right, use ls, simp [ih hls] } }
end

theorem mem_explode_iff_map_var_eq {l : list V} {c : clause V} : 
  c.map var = l ↔ c ∈ explode l :=
⟨mem_explode_of_map_var_eq, map_var_eq_of_mem_explode⟩

-- Some way of compressing casework into a "repeat"?
-- TODO think about pulling c, c ∈ explode into hypotheses to remove "of_mem_explode"
lemma mem_clause_of_mem_of_mem_explode {l : list V} : 
  ∀ {c : clause V}, c ∈ explode l → ∀ {v : V}, v ∈ l → Pos v ∈ c ∨ Neg v ∈ c :=
begin
  induction l with m ms ih,
  { simp },
  simp only [explode, mem_append, mem_map],
  rintros c (⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩) n (rfl | hn),
  { simp [mem_cons_self] },
  { cases ih hd hn with h h; 
    simp [mem_cons_of_mem _ h] },
  { simp [mem_cons_self] },
  { cases ih hd hn with h h; 
    simp [mem_cons_of_mem _ h] }
end

-- Reduce casework?
lemma mem_of_mem_clause_of_mem_explode {l : list V} :
  ∀ {c : clause V}, c ∈ explode l → ∀ {v : V}, Pos v ∈ c ∨ Neg v ∈ c → v ∈ l :=
begin
  induction l with m ms ih,
  { simp },
  simp only [explode, mem_append, mem_map],
  rintros c (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) n (hn | hn),
  { rcases eq_or_mem_of_mem_cons hn with (hn₁ | hn₂),
    { have := congr_arg literal.var hn₁,
      simp [var] at this,
      simp [this] },
    { exact mem_cons_of_mem _ (ih ha (or.inl hn₂)) } },
  { rcases eq_or_mem_of_mem_cons hn with (hn₁ | hn₂),
    { have := congr_arg literal.var hn₁,
      simp [var] at this,
      simp [this] },
    { exact mem_cons_of_mem _ (ih ha (or.inr hn₂)) } },
  { rcases eq_or_mem_of_mem_cons hn with (hn₁ | hn₂),
    { have := congr_arg literal.var hn₁,
      simp [var] at this,
      simp [this] },
    { exact mem_cons_of_mem _ (ih ha (or.inl hn₂)) } },
  { rcases eq_or_mem_of_mem_cons hn with (hn₁ | hn₂),
    { have := congr_arg literal.var hn₁,
      simp [var] at this,
      simp [this] },
    { exact mem_cons_of_mem _ (ih ha (or.inr hn₂)) } }
end

theorem mem_iff_mem_clause_of_mem_explode {l : list V} :
  ∀ {c : clause V}, c ∈ explode l → ∀ {v : V}, Pos v ∈ c ∨ Neg v ∈ c ↔ v ∈ l :=
assume c hc n, ⟨mem_of_mem_clause_of_mem_explode hc, 
                mem_clause_of_mem_of_mem_explode hc⟩

-- Corollaries of the above
theorem mem_var_of_mem_clause_of_mem_explode {l : list V} :
  ∀ {c : clause V}, c ∈ explode l → ∀ {lit : literal V}, lit ∈ c → literal.var lit ∈ l :=
begin
  intros c hc lit hl,
  cases lit,
  { simp [var, mem_of_mem_clause_of_mem_explode hc (or.inl hl)] },
  { simp [var, mem_of_mem_clause_of_mem_explode hc (or.inr hl)] }
end

theorem not_mem_clause_of_not_mem_of_mem_explode {l : list V} : 
  ∀ {c : clause V}, c ∈ explode l → ∀ {v : V}, v ∉ l → Pos v ∉ c ∧ Neg v ∉ c :=
begin
  intros c hc n,
  contrapose,
  simp [not_and_distrib],
  exact mem_of_mem_clause_of_mem_explode hc
end

theorem not_mem_of_not_mem_clause_of_mem_explode {l : list V} : 
  ∀ {c : clause V}, c ∈ explode l → ∀ {v : V}, (Pos v ∉ c) ∧ (Neg v ∉ c) → v ∉ l :=
begin
  intros c hc n,
  contrapose,
  simp [not_and_distrib],
  exact mem_clause_of_mem_of_mem_explode hc
end

/-! # nodup properties of explode -/

theorem explode_nodup (l : list V) : nodup (explode l) :=
begin
  induction l with n ns ih,
  { simp },
  { simp [explode, nodup_cons],
    apply nodup_append.mpr,
    simp [nodup_map (cons_injective) ih],
    intros x hx hxn,
    rcases mem_map.mp hx with ⟨c, hc, hcx⟩,
    rcases mem_map.mp hxn with ⟨d, hd, hdx⟩,
    rw ← hcx at hdx,
    exact absurd (head_eq_of_cons_eq hdx).symm (pos_ne_neg n) }
end

-- This can be made into a non-induction argument
theorem mem_nodup_of_nodup {l : list V} (h : nodup l) :
  ∀ {c : clause V}, c ∈ explode l → nodup c :=
begin
  induction l with n ns ih,
  { simp },
  { intros c hc,
    simp [explode] at hc,
    rcases hc with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩;
    { rcases not_mem_clause_of_not_mem_of_mem_explode 
        ha (not_mem_of_nodup_cons h) with ⟨hpos, hneg⟩,
      simp [hpos, hneg, ih (nodup_of_nodup_cons h) ha] } }
end

theorem xor_mem_clause_of_mem_of_mem_explode {l : list V} (h : nodup l) :
  ∀ {c : clause V}, c ∈ explode l → ∀ {v : V}, v ∈ l → xor (Pos v ∈ c) (Neg v ∈ c) :=
begin
  induction l with m ms ih,
  { simp },
  { intros c hc n hn,
    simp [explode] at hc,
    rcases hc with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩;
    { rcases eq_or_mem_of_mem_cons hn with (rfl | hn),
      { simp [mem_cons_self, 
        not_mem_clause_of_not_mem_of_mem_explode ha (not_mem_of_nodup_cons h)] },
      { rcases ih (nodup_of_nodup_cons h) ha hn with ⟨hpos, hneg⟩ | ⟨hpos, hneg⟩;
        { simp [hpos, hneg, ne_of_mem_of_not_mem hn (not_mem_of_nodup_cons h)] } } } }
end

end explode