/-
This file defines various Boolean cardinality constraints.

Authors: Cayden Codel, Jeremy Avigad, Marijn Heule
Carnegie Mellon University
-/

import cnf.literal
import cnf.assignment
import cnf.cnf
import cnf.encoding
import cardinality.distinct

universe u

variables {V : Type*} [decidable_eq V] [inhabited V]

def amz (l : list bool) : bool := l.count tt = 0

namespace amz

open literal
open clause
open list
open assignment
open encoding

@[simp] theorem amz_nil : amz [] = tt := rfl

@[simp] theorem amz_tt_iff_forall_mem_eq_ff {l : list bool} :
  amz l = tt ↔ ∀ b ∈ l, b = ff :=
begin
  rw [amz, to_bool_iff],
  split,
  { intros h b hb,
    cases b,
    { refl },
    { exact absurd hb (not_mem_of_count_eq_zero h) } },
  { intro h,
    apply count_eq_zero_of_not_mem,
    intro hl,
    have := h tt hl,
    contradiction }
end

protected def eval (τ : assignment V) (l : list (literal V)) : bool :=
  amz (l.map (literal.eval τ))

@[simp] theorem eval_nil (τ : assignment V) : amz.eval τ [] = tt :=
by simp only [amz, amz.eval, count_nil, to_bool_true_eq_tt, eq_self_iff_true, map_nil]

theorem eval_tt_iff_forall_eval_ff {τ : assignment V} {l : list (literal V)} :
  amz.eval τ l = tt ↔ ∀ lit ∈ l, literal.eval τ lit = ff :=
begin
  split,
  { intro h,
    rw [amz.eval, amz, to_bool_iff] at h,
    have := mt mem_map.mpr (not_mem_of_count_eq_zero h),
    simp at this,
    exact this },
  { intro h,
    rw [amz.eval, amz, to_bool_iff, count_eq_zero_of_not_mem],
    intro hcon,
    rcases mem_map.mp hcon with ⟨lit, hmem, heval⟩,
    rw h lit hmem at heval,
    contradiction }
end

theorem eval_ff_iff_exists_eval_tt {τ : assignment V} {l : list (literal V)} :
  amz.eval τ l = ff ↔ ∃ lit ∈ l, literal.eval τ lit = tt :=
begin
  split,
  { contrapose,
    simpa using eval_tt_iff_forall_eval_ff.mpr },
  { contrapose,
    simpa using eval_tt_iff_forall_eval_ff.mp }
end

theorem eval_tt_of_eval_tt_cons {τ : assignment V} {l : list (literal V)} 
  {lit : literal V} : amz.eval τ (lit :: l) = tt → amz.eval τ l = tt :=
begin
  intro h,
  rw eval_tt_iff_forall_eval_ff at h,
  apply eval_tt_iff_forall_eval_ff.mpr,
  intros lit hl,
  exact h lit (mem_cons_of_mem _ hl)
end

theorem eval_cons_eq_of_eval_ff {τ : assignment V} {l : list (literal V)}
  {lit : literal V} : lit.eval τ = ff → amz.eval τ (lit :: l) = amz.eval τ l :=
begin
  intro h,
  simp only [amz.eval, amz, h, map, count_cons_of_ne, ne.def, not_false_iff]
end

-- Encoding of at-most-zero is a clause for each literal, negated
def direct_amz (l : list (literal V)) : cnf V := l.map (λ x, [literal.flip x])

theorem direct_amz_encodes_amz (l : list (literal V)) :
  l ≠ [] → encodes amz (direct_amz l) l :=
begin
  rw direct_amz,
  intros hnil τ,
  rcases exists_mem_of_ne_nil l hnil with ⟨lit, hlit⟩,
  split,
  { intro h,
    use τ,
    split,
    { rw cnf.eval_tt_iff_forall_clause_eval_tt,
      intros c hc,
      rcases mem_map.mp hc with ⟨lit₂, hlit₂, rfl⟩,
      rw eval_singleton,
      rw eval_flip,
      simp only [amz, to_bool_iff] at h,
      have := mt (mem_map.mpr) (not_mem_of_count_eq_zero h),
      simp only [not_exists, eq_ff_eq_not_eq_tt, not_and] at this,
      simp only [this lit₂ hlit₂, bool.bnot_false] },
    { exact eqod.refl τ _ } },
  { rintros ⟨σ, heval, heqod⟩,
    rw cnf.eval_tt_iff_forall_clause_eval_tt at heval,
    simp [amz],
    simp at heval,
    apply count_eq_zero_of_not_mem,
    simp [mem_map],
    intros lit₂ hlit₂,
    have := mem_vars_of_mem hlit₂,
    rw eval_eq_of_eqod_of_var_mem heqod this,
    have := heval lit₂ hlit₂,
    simpa [eval_flip] using this }
end

-- TODO: There's a way to get a direct proof
theorem eval_eq_amz_of_eqod {τ₁ τ₂ : assignment V} {l : list (literal V)} :
  (τ₁ ≡clause.vars l≡ τ₂) → amz.eval τ₁ l = amz.eval τ₂ l :=
begin
  intro heqod,
  induction l with l ls ih,
  { simp only [amz.eval_nil] },
  { have : literal.eval τ₁ l = literal.eval τ₂ l,
    { have := mem_vars_of_mem (mem_cons_self l ls),
      exact eval_eq_of_eqod_of_var_mem heqod this },
    cases h : (literal.eval τ₁ l),
    { rw eval_cons_eq_of_eval_ff h,
      rw this at h,
      rw eval_cons_eq_of_eval_ff h,
      exact ih (eqod_subset (vars_subset_of_vars_cons l ls) heqod) },
    { rw eval_ff_iff_exists_eval_tt.mpr ⟨l, mem_cons_self l ls, h⟩,
      rw this at h,
      rw eval_ff_iff_exists_eval_tt.mpr ⟨l, mem_cons_self l ls, h⟩ } }
end

end amz

def amo (l : list bool) : bool := l.count tt ≤ 1

namespace amo

open amz
open literal
open clause
open assignment
open list
open encoding
open nat
open distinct

@[simp] theorem amo_nil : amo [] = tt := rfl

@[simp] theorem amo_singleton (b : bool) : amo [b] = tt :=
by cases b; simp [amo]

theorem amo_cons_pos (l : list bool) : amo (tt :: l) = amz l :=
begin
  simp only [amo, amz, count_cons_self, bool.to_bool_eq, succ_le_succ_iff],
  exact le_zero_iff
end

theorem amo_cons_neg {l : list bool} : amo (ff :: l) = amo l :=
by simp only [amo, count_cons_of_ne, ne.def, not_false_iff]

protected def eval (τ : assignment V) (l : list (literal V)) : bool := 
  amo (l.map (literal.eval τ))

-- TODO see if theorems can be tightend up with intro of amo_XX above
@[simp] theorem eval_nil (τ : assignment V) : amo.eval τ [] = tt :=
by simp only [amo.eval, amo, zero_le_one, count_nil, to_bool_true_eq_tt, map_nil]

@[simp] theorem eval_singleton (τ : assignment V) (lit : literal V) : 
  amo.eval τ [lit] = tt :=
by { simp only [amo.eval, amo, map, to_bool_iff], exact count_le_length _ _ }

theorem eval_cons_pos {τ : assignment V} {l : list (literal V)} {lit : literal V} : 
  lit.eval τ = tt → amo.eval τ (lit :: l) = amz.eval τ l :=
begin
  intro h,
  simp [amo.eval, amo, amz.eval, amz, h],
  split,
  { intro hl,
    rw ← zero_add 1 at hl,
    exact le_zero_iff.mp (succ_le_succ_iff.mp hl) },
  { intro hl,
    exact le_of_eq (congr_arg succ hl) }
end

theorem eval_cons_neg {τ : assignment V} {l : list (literal V)} {lit : literal V} : 
  lit.eval τ = ff → amo.eval τ (lit :: l) = amo.eval τ l :=
begin
  intro h,
  rw [amo.eval, amo, map_cons, h, count_cons],
  simp only [if_false],
  refl
end

theorem eval_tt_of_amz_eval_tt {τ : assignment V} {l : list (literal V)} :
  amz.eval τ l = tt → amo.eval τ l = tt :=
begin
  simp only [amz.eval, amz, amo.eval, amo, to_bool_iff],
  intro h,
  rw h,
  exact zero_le_one
end

theorem eval_tt_of_eval_tt_cons {τ : assignment V} {lit : literal V} {l : list (literal V)} :
  amo.eval τ (lit :: l) = tt → amo.eval τ l = tt :=
begin
  cases h : (literal.eval τ lit),
  { rw eval_cons_neg h, exact id },
  { rw eval_cons_pos h, exact eval_tt_of_amz_eval_tt }
end

theorem eval_cons_tt_of_amz_eval_tt {τ : assignment V} {l : list (literal V)} 
  {lit : literal V} : amz.eval τ l = tt → amo.eval τ (lit :: l) = tt :=
begin
  intro h,
  cases hlit : literal.eval τ lit,
  { rw eval_cons_neg hlit,
    exact eval_tt_of_amz_eval_tt h },
  { rw eval_cons_pos hlit,
    exact h }
end

theorem exists_eval_tt_of_eval_tt_of_amz_eval_ff {τ : assignment V} {l : list (literal V)} :
  amo.eval τ l = tt → amz.eval τ l = ff → ∃ lit ∈ l, literal.eval τ lit = tt :=
begin
  induction l with l₁ ls ih,
  { intros h₁ h₂, simp [amz.eval] at h₂, contradiction },
  { intros ho hz,
    cases h: l₁.eval τ,
    { rw eval_cons_neg h at ho,
      rw eval_cons_eq_of_eval_ff h at hz,
      rcases ih ho hz with ⟨w, hmem, hw⟩,
      use ⟨w, (mem_cons_of_mem _ hmem), hw⟩ },
    { use ⟨l₁, mem_cons_self _ _, h⟩ } }
end

theorem amo_eval_tt_iff_distinct_eval_ff_of_eval_tt {τ : assignment V} {l : list (literal V)} :
  amo.eval τ l = tt ↔ (∀ {lit₁ lit₂ : literal V}, 
  distinct lit₁ lit₂ l → lit₁.eval τ = tt → lit₂.eval τ = ff) :=
begin
  induction l with l₁ ls ih,
  { split,
    { intros _ lit₁ lit₂ hdis,
      exact absurd hdis (not_distinct_nil _ _) },
    { rw eval_nil, tautology } },
  { cases ls with l₂ ls,
    { split,
      { intros _ lit₁ lit₂ hdis,
        exact absurd hdis (not_distinct_singleton _ _ _) },
      { rw eval_singleton, tautology } },
    { split,
      { intros heval lit₁ lit₂ hdis h₁,
        have hmem₂ := mem_tail_of_distinct_cons hdis,
        rcases hdis with ⟨i, j, hi, hj, hij, hil, hjl⟩,
        cases i,
        { rw nth_le at hil,
          rw [hil, eval_cons_pos h₁, eval_tt_iff_forall_eval_ff] at heval,
          exact heval lit₂ hmem₂ },
        { cases j,
          { linarith },
          { have : distinct lit₁ lit₂ (l₂ :: ls),
            { rw [length, succ_lt_succ_iff] at hi hj,
              rw succ_lt_succ_iff at hij,
              rw nth_le at hil hjl,
              exact ⟨i, j, hi, hj, hij, hil, hjl⟩ },
            cases h : (literal.eval τ l₁),
            { rw eval_cons_neg h at heval,
              exact ih.mp heval this h₁ },
            { rw [eval_cons_pos h, eval_tt_iff_forall_eval_ff] at heval,
              exact heval lit₂ hmem₂ } } } },
      { intro h,
        cases h₁ : (literal.eval τ l₁),
        { rw eval_cons_neg h₁,
          apply ih.mpr,
          intros lit₁ lit₂ hdis' h₁',
          exact h (distinct_cons_of_distinct l₁ hdis') h₁' },
        { rw [eval_cons_pos h₁, eval_tt_iff_forall_eval_ff],
          intros x hx,
          exact h (distinct_cons_of_mem l₁ hx) h₁ } } } }
end

-- TODO: Direct proof?
theorem eval_eq_amo_of_eqod {τ₁ τ₂ : assignment V} {l : list (literal V)} :
  (τ₁ ≡clause.vars l≡ τ₂) → amo.eval τ₁ l = amo.eval τ₂ l :=
begin
  induction l with l ls ih,
  { rw [eval_nil, eval_nil], tautology },
  { intro heqod,
    have heq : literal.eval τ₁ l = literal.eval τ₂ l,
    { have := mem_vars_of_mem (mem_cons_self l ls),
      exact eval_eq_of_eqod_of_var_mem heqod this },
    have := eqod_subset (vars_subset_of_vars_cons l ls) heqod,
    cases h : (literal.eval τ₁ l),
    { rw eval_cons_neg h,
      rw heq at h,
      rw eval_cons_neg h,
      exact ih this },
    { rw eval_cons_pos h,
      rw heq at h,
      rw eval_cons_pos h,
      exact eval_eq_amz_of_eqod this } }
end

-- Sinz encoding: art of computer programming
-- Sinz paper as well, Marijn has 20 lines of C code
-- Sorting networks (Stanford)

--------------------------------------------------------------------------------
-- Direct AMO encoding
--------------------------------------------------------------------------------

def direct_amo : list (literal V) → cnf V
| []        := []
| (l :: ls) := (ls.map (λ m, [l.flip, m.flip])) ++ (direct_amo ls)

@[simp] theorem direct_amo_nil : direct_amo ([] : list (literal V)) = [] := rfl

@[simp] theorem direct_amo_singleton (lit : literal V) : 
  direct_amo [lit] = [] := rfl

@[simp] theorem direct_amo_double (l₁ l₂ : literal V) :
  direct_amo [l₁, l₂] = [[l₁.flip, l₂.flip]] := rfl

theorem exists_mem_of_length_ge_two :
  ∀ {l : list (literal V)}, length l ≥ 2 → ∃ (c : clause V), c ∈ direct_amo l
| []   hl := by { rw length at hl, linarith }
| [l₁] hl := by { rw [length, length] at hl, linarith }
| (l₁ :: l₂ :: ls) hl := begin
  use [[l₁.flip, l₂.flip]],
  rw [direct_amo, mem_append], left,
  simp only [map, mem_cons_iff, eq_self_iff_true, true_or]
end

theorem length_eq_two_of_mem {l : list (literal V)} {c : clause V} (hl : length l ≥ 2) :
  c ∈ direct_amo l → length c = 2 :=
begin
  induction l with l₁ ls ih,
  { rw length at hl, linarith },
  { rw direct_amo,
    simp only [mem_map, mem_append],
    by_cases hls : length ls = 1,
    { rcases exists_of_length_succ ls hls with ⟨l₂, ls, rfl⟩,
      simp [length_eq_zero] at hls,
      simp [hls],
      rintro rfl,
      dec_trivial },
    { rw length at hl,
      have := succ_le_succ_iff.mp hl,
      have : 1 < ls.length, exact (ne.symm hls).le_iff_lt.mp this,
      have : 2 ≤ ls.length, exact succ_le_iff.mpr this,
      rintros (⟨a, ha, rfl⟩ | h),
      { dec_trivial },
      { exact ih this h } } }
end

-- TODO rename, distinct isn't used here
theorem exists_double_flip_eq_of_mem {l : list (literal V)} {c : clause V} (hl : length l ≥ 2) :
  c ∈ direct_amo l → ∃ (lit₁ lit₂ : literal V), [lit₁.flip, lit₂.flip] = c :=
begin
  intro h,
  rcases exists_cons_cons_of_length_eq_two (length_eq_two_of_mem hl h) with ⟨lit₁, lit₂, rfl⟩,
  use [lit₁.flip, lit₂.flip],
  rw [flip_flip, flip_flip]
end

-- TODO this feels like a very long proof, can probably be shortened
theorem distinct_iff_mem {l : list (literal V)} {lit₁ lit₂ : literal V} :
  distinct lit₁ lit₂ l ↔ [lit₁.flip, lit₂.flip] ∈ direct_amo l :=
begin
  split,
  { induction l with l₁ ls ih,
    { intro h, exact absurd h (not_distinct_nil _ _) },
    { intro h,
      have hdis := h,
      have hl := length_ge_two_of_distinct h,
      rcases exists_cons_cons_of_length_ge_two hl with ⟨a₁, a₂, L, hL⟩,
      rw ← (tail_eq_of_cons_eq hL) at *,
      rw [direct_amo, mem_append],
      rcases h with ⟨i, j, hi, hj, hij, hil, hjl⟩,
      cases i,
      { rw nth_le at hil,
        left,
        rw [hil, mem_map],
        use [lit₂, mem_tail_of_distinct_cons hdis] },
      { have : distinct lit₁ lit₂ (a₂ :: L),
        { rw length at hi,
          have := succ_le_iff.mpr ((gt_of_gt_of_ge hij (zero_le i.succ))),
          rcases nth_le_of_ge hj this with ⟨h₁, h₂⟩,
          rw length at h₁,
          rw distinct,
          use [i, j - 1, succ_lt_succ_iff.mp hi, succ_lt_succ_iff.mp h₁],
          split,
          { rw ← nat.sub_add_cancel this at hij,
            exact succ_lt_succ_iff.mp hij },
          rw nth_le at hil,
          rw [hjl, nth_le] at h₂,
          exact ⟨hil, h₂.symm⟩ },
        exact or.inr (ih this) } } },
  { induction l with l₁ ls ih,
    { simp only [direct_amo_nil, not_mem_nil, forall_false_left] },
    { cases ls with l₂ ls,
      { rw direct_amo_singleton, intro h, exact absurd h (not_mem_nil _) },
      cases ls with l₃ ls,
      { rw [direct_amo_double, mem_singleton],
        simp only [eq_self_iff_true, and_true, and_imp],
        intros h₁ h₂,
        rw [flip_inj.mp h₁, flip_inj.mp h₂],
        use [0, 1], simp },
      { intro h, -- TODO this feels very casewise
        rw [direct_amo, mem_append] at h,
        rcases h with (h | h),
        { simp at h,
          rcases h with (⟨h₁, h₂⟩ | ⟨h₁, h₃⟩ | ⟨l₄, hl₄, h₁, hls⟩),
          { rw [flip_inj.mp h₁, flip_inj.mp h₂],
            use [0, 1], simp },
          { rw [flip_inj.mp h₁, flip_inj.mp h₃],
            use [0, 2], simp, linarith }, -- can be done explicitly rather than linarith
          { rw [flip_inj.mp h₁, ← flip_inj.mp hls],
            rcases nth_le_of_mem hl₄ with ⟨n, hn, hln₄⟩,
            use [0, n + 3],
            simp,
            use [succ_lt_succ (succ_lt_succ (succ_lt_succ hn)), hln₄] } },
        { have : (l₂ :: l₃ :: ls).length ≥ 2,
          { rw [length, length], linarith },
          exact distinct_cons_of_distinct l₁ (ih h) } } } }
end

-- NOTE: unfortunately, subset doesn't work because ordering of vars in clauses
theorem subset_direct_of_sublist {l₁ l₂ : list (literal V)} :
  l₁ <+ l₂ → (direct_amo l₁) ⊆ (direct_amo l₂) :=
begin
  induction l₂ with lit₁ ls ih generalizing l₁,
  { rw sublist_nil_iff_eq_nil, rintro rfl, exact subset.refl _ },
  { intros hl₁ c hc,
    cases hl₁,
    { rw [direct_amo, mem_append],
      exact or.inr ((ih hl₁_ᾰ) hc) },
    { rw [direct_amo, mem_append] at hc,
      rcases hc with (hc | hc),
      { rw mem_map at hc,
        rcases hc with ⟨a, hal, hac⟩,
        rw [direct_amo, mem_append, mem_map],
        exact or.inl ⟨a, sublist.subset hl₁_ᾰ hal, hac⟩ },
      { rw [direct_amo, mem_append],
        exact or.inr (ih hl₁_ᾰ hc) } } }
end

theorem eval_tt_iff_forall_distinct_eval_ff {τ : assignment V} 
  {l : list (literal V)} : length l ≥ 2 → ((direct_amo l).eval τ = tt ↔ 
   (∀ {lit₁ lit₂ : literal V}, (distinct lit₁ lit₂ l) → lit₁.eval τ = ff ∨ lit₂.eval τ = ff)) :=
begin
  intro hl,
  split,
  { intros heval lit₁ lit₂ hdis,
    rw cnf.eval_tt_iff_forall_clause_eval_tt at heval,
    have := heval [lit₁.flip, lit₂.flip] (distinct_iff_mem.mp hdis),
    rw eval_tt_iff_exists_literal_eval_tt at this,
    rcases this with ⟨lit, hmem, hlit⟩,
    simp only [mem_cons_iff, mem_singleton] at hmem,
    rcases hmem with (rfl | rfl),
    { rw eval_flip at hlit,
      exact or.inl (bool.eq_ff_of_bnot_eq_tt hlit) },
    { rw eval_flip at hlit,
      exact or.inr (bool.eq_ff_of_bnot_eq_tt hlit) } },
  { intro h,
    rw cnf.eval_tt_iff_forall_clause_eval_tt,
    intros c hc,
    rcases exists_double_flip_eq_of_mem hl hc with ⟨l₁, l₂, rfl⟩,
    have := h (distinct_iff_mem.mpr hc),
    rw eval_tt_iff_exists_literal_eval_tt,
    rcases h (distinct_iff_mem.mpr hc) with (hff | hff),
    { use l₁.flip,
      simp [eval_flip_of_eval hff] },
    { use l₂.flip,
      simp [eval_flip_of_eval hff] } }
end

theorem eval_tt_iff_forall_distinct_eval_ff_of_eval_tt {τ : assignment V} 
  {l : list (literal V)} : length l ≥ 2 → ((direct_amo l).eval τ = tt ↔ 
   (∀ {lit₁ lit₂ : literal V}, (distinct lit₁ lit₂ l) → lit₁.eval τ = tt → lit₂.eval τ = ff)) :=
begin
  intro hl,
  split,
  { intros ht lit₁ lit₂ hdis hlit₁, 
    rcases (eval_tt_iff_forall_distinct_eval_ff hl).mp ht hdis with (h | h),
    { rw h at hlit₁, contradiction },
    { exact h } },
  { intro hls,
    apply (eval_tt_iff_forall_distinct_eval_ff hl).mpr,
    intros lit₁ lit₂ hdis,
    cases h : (literal.eval τ lit₁),
    { exact or.inl (refl ff) },
    { exact or.inr (hls hdis h) } }
end

theorem eval_ff_iff_forall_distinct_eval_tt {τ : assignment V}
  {l : list (literal V)} (hl : length l ≥ 2) :
  ((direct_amo l).eval τ = ff ↔ 
  (∃ {lit₁ lit₂ : literal V}, (distinct lit₁ lit₂ l) ∧ lit₁.eval τ = tt ∧ lit₂.eval τ = tt)) :=
begin
  split,
  { rw cnf.eval_ff_iff_exists_clause_eval_ff,
    rintros ⟨c, hmem, hc⟩,
    rcases exists_double_flip_eq_of_mem hl hmem with ⟨lit₁, lit₂, rfl⟩,
    rw eval_ff_iff_forall_literal_eval_ff at hc,
    use [lit₁, lit₂, distinct_iff_mem.mpr hmem],
    have h₁ : lit₁.flip ∈ [lit₁.flip, lit₂.flip], from mem_cons_self _ _,
    have h₂ : lit₂.flip ∈ [lit₁.flip, lit₂.flip], simp,
    have h₁eval := eval_flip_of_eval (hc lit₁.flip h₁),
    have h₂eval := eval_flip_of_eval (hc lit₂.flip h₂),
    rw flip_flip at h₁eval h₂eval,
    exact ⟨h₁eval, h₂eval⟩ },
  { rintro ⟨lit₁, lit₂, hdis, h₁, h₂⟩,
    rw cnf.eval_ff_iff_exists_clause_eval_ff,
    use [[lit₁.flip, lit₂.flip], distinct_iff_mem.mp hdis],
    rw eval_ff_iff_forall_literal_eval_ff,
    simp [h₁, h₂, eval_flip] }
end

theorem direct_amo_encodes_amo :
  ∀ {l : list (literal V)}, l ≠ [] → encodes amo (direct_amo l) l
| [] hnil := by contradiction
| [l₁] _  := by { intro τ, simp, use τ }
| (l₁ :: l₂ :: ls) _ := begin
  have hl : length (l₁ :: l₂ :: ls) ≥ 2, dec_trivial,
  intro τ, split,
  { intro hamo,
    rw ← amo.eval at hamo,
    rw amo_eval_tt_iff_distinct_eval_ff_of_eval_tt at hamo,
    use τ,
    split,
    { rw cnf.eval_tt_iff_forall_clause_eval_tt,
      intros c hc,
      rw eval_tt_iff_exists_literal_eval_tt,
      rcases exists_double_flip_eq_of_mem hl hc with ⟨lit₁, lit₂, rfl⟩,
      cases h : (lit₁.eval τ),
      { use [lit₁.flip, mem_cons_self _ _],
        rw eval_flip,
        simp only [h, bool.bnot_false] },
      { have : lit₂.flip ∈ [lit₁.flip, lit₂.flip], simp,
        use [lit₂.flip, this],
        exact eval_flip_of_eval (hamo (distinct_iff_mem.mpr hc) h) } },
    { exact eqod.refl _ _ } },
  { rintros ⟨σ, heval, hsigma⟩,
    rw cnf.eval_tt_iff_forall_clause_eval_tt at heval,
    rw ← amo.eval,
    rw amo_eval_tt_iff_distinct_eval_ff_of_eval_tt,
    intros lit₁ lit₂ hdis h₁,
    have := heval _ (distinct_iff_mem.mp hdis),
    rw eval_tt_iff_exists_literal_eval_tt at this,
    rcases this with ⟨lit, hmem, hlit⟩,
    simp at hmem,
    rcases hmem with (rfl | rfl),
    { have := mem_vars_of_mem (mem_of_distinct_left hdis),
      rw eval_eq_of_eqod_of_var_mem hsigma this at h₁,
      rw [eval_flip, h₁] at hlit,
      contradiction },
    { have := mem_vars_of_mem (mem_of_distinct_right hdis),
      have h₂ := eval_flip_of_eval hlit,
      rw flip_flip at h₂,
      rw ← eval_eq_of_eqod_of_var_mem hsigma this at h₂,
      exact h₂ } }
end

/-
protected def eval : bool := Xor (l.map (literal.eval τ))

@[simp] theorem eval_nil : Xor.eval τ [] = ff := rfl

@[simp] theorem eval_singleton : Xor.eval τ [lit] = lit.eval τ :=
by simp only [Xor.eval, Xor, map, bool.bxor_ff_right, foldr]

theorem eval_cons : Xor.eval τ (lit :: l) = bxor (lit.eval τ) (Xor.eval τ l) :=
by simp only [Xor.eval, Xor, foldr, foldr_map]

theorem eval_append : 
  Xor.eval τ (l₁ ++ l₂) = bxor (Xor.eval τ l₁) (Xor.eval τ l₂) :=
begin
  induction l₁ with l ls ih,
  { simp only [bool.bxor_ff_left, eval_nil, nil_append] },
  { simp only [eval_cons, ih, cons_append, bool.bxor_assoc] }
end

/- Evaluates to true if an odd number of literals evaluates to true -/
theorem eval_eq_bodd_count_tt : Xor.eval τ l = bodd (clause.count_tt τ l) :=
begin
  induction l with l ls ih,
  { simp only [bodd_zero, eval_nil, count_tt_nil] },
  { cases h : (l.eval τ); { simp [Xor.eval_cons, count_tt_cons, h, ih] } }
end
-/

end amo

def amk (k : nat) (l : list bool) : bool := l.count tt ≤ k

namespace amk

open list

protected def eval (k : nat) (τ : assignment V) (l : list (literal V)) : bool :=
  amk k (l.map (literal.eval τ))

variables (k : nat) (τ : assignment V) (l : list (literal V)) (lit : literal V)

@[simp] theorem eval_nil : amk.eval k τ [] = tt :=
by simp only [amk.eval, amk, count_nil, to_bool_true_eq_tt, zero_le, map_nil]

@[simp] theorem amk_zero_eq_amz : amk.eval 0 τ l = amz.eval τ l :=
by simp only [amk.eval, amk, amz.eval, amz, nonpos_iff_eq_zero]

@[simp] theorem amk_one_eq_amo : amk.eval 1 τ l = amo.eval τ l :=
by simp only [amk.eval, amk, amo.eval, amo]

theorem eval_cons_pos_of_gt_zero {k : nat} {τ : assignment V} 
  {l : list (literal V)} {lit : literal V} : 
  k > 0 → lit.eval τ = tt → amk.eval k τ (lit :: l) = amk.eval (k - 1) τ l :=
begin
  intro hk,
  cases k,
  { exact absurd hk (asymm hk) },
  { intro ht,
    simp [amk.eval, amk, ht, nat.succ_le_succ_iff] }
end

end amk