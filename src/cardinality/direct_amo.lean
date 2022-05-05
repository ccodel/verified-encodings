/-
The direct encoding for the at-most-one function.

Authors: Cayden Codel, Jeremy Avigad, Marijn Heule
Carnegie Mellon University
-/

import cnf.literal
import cnf.assignment
import cnf.clause
import cnf.cnf
import cnf.encoding

import cardinality.amk
import cardinality.distinct

variables {V : Type*} [decidable_eq V] [inhabited V]

open list
open nat
open amk
open clause
open assignment
open literal
open cnf
open distinct
open encoding

namespace direct_amo

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

theorem direct_amo_encodes_amo : ∀ (l : list (literal V)),
  encodes (amk 1) (direct_amo l) l
| []   := by { intro τ, simp, }
| [l₁] := by { intro τ, simp [← amk.eval], use τ }
| (l₁ :: l₂ :: ls) := begin
  have hl : length (l₁ :: l₂ :: ls) ≥ 2, dec_trivial,
  intro τ, split,
  { intro hamk, rw ← amk.eval at hamk,
    rw amo_eval_tt_iff_distinct_eval_ff_of_eval_tt at hamk,
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
        exact eval_flip_of_eval (hamk (distinct_iff_mem.mpr hc) h) } },
    { exact eqod.refl _ _ } },
  { rintros ⟨σ, heval, hsigma⟩,
    rw cnf.eval_tt_iff_forall_clause_eval_tt at heval,
    rw ← amk.eval,
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

end direct_amo