/-

  Some basic facts unrelated to literals, clauses, etc. that are useful for proofs.

  Author: Cayden Codel
  Carnegie Mellon University

-/

import data.bool
import data.list.basic
import data.list.nodup
import init.data.nat.lemmas
import tactic

import init.function

open list
open function

universes u v
variables {α : Type u} {β : Type v}

-- Define shorthand for XOR
notation a ` ⊕ ` b := bxor a b

-- Some trivial, useful theorems
@[simp] theorem bxor_tt_left  : ∀ a, bxor tt a = bnot a := dec_trivial
@[simp] theorem bxor_tt_right : ∀ a, bxor a tt = bnot a := dec_trivial

@[simp] theorem cond_tt_ff : ∀ a, cond a tt ff = a := dec_trivial
@[simp] theorem cond_ff_tt : ∀ a, cond a ff tt = bnot a := dec_trivial

theorem tt_of_cond_ne_second [decidable_eq α] {c d : α} {b : bool} :
  cond b c d ≠ d → b = tt :=
by cases b; simp

theorem ff_of_cond_ne_first [decidable_eq α] {c d : α} {b : bool} :
  cond b c d ≠ c → b = ff :=
by cases b; simp

theorem tt_of_cond_eq_of_ne_second [decidable_eq α] {c d e : α} {b : bool} :
  d ≠ e → cond b c d = e → b = tt :=
begin
  cases b,
  { simp, exact id },
  { tautology }
end

theorem ff_of_cond_eq_of_ne_first [decidable_eq α] {c d e : α} {b : bool} :
  c ≠ e → cond b c d = e → b = ff :=
begin
  cases b,
  { tautology },
  { simp, exact id }
end

theorem band_tt_of_and_tt {b₁ b₂ : bool} : b₁ = tt ∧ b₂ = tt → b₁ && b₂ = tt :=
begin
  rintros ⟨h₁, h₂⟩,
  simp [h₁, h₂]
end

-- Expand xor in terms of other boolean operations
-- (Proof seems inane - shorten?)
theorem bxor_conjunctive : ∀ (a b : bool), bxor a b = (a || b) && (!a || !b)
| tt tt := dec_trivial
| tt ff := dec_trivial
| ff tt := dec_trivial
| ff ff := dec_trivial

theorem bxor_disjunctive : ∀ (a b : bool), bxor a b = (!a && b) || (a && !b)
| tt tt := dec_trivial
| tt ff := dec_trivial
| ff tt := dec_trivial
| ff ff := dec_trivial

theorem neq_of_ff_of_tt {a b : bool} : a = tt → b = ff → a ≠ b :=
begin
  intros ha hb, simp [ha, hb]
end

/- This is a shorthand for absurd that derives from a boolean that is true and false -/
theorem absurd_bool {a : bool} {b : Prop} : a = tt → a = ff → b :=
assume h₁ h₂, absurd h₁ (neq_of_ff_of_tt rfl h₂).symm

/- Reasoning about cond is helpful if the result of the cond is known -/
theorem cond_tt_of_cond_eq_first_of_ne [decidable_eq α] {a₁ a₂ : α} (b : bool) : 
  a₂ ≠ a₂ → cond b a₁ a₂ = a₁ → b = tt :=
by cases b; simp [imp_false]

theorem cond_ff_of_cond_eq_second_of_ne [decidable_eq α] {a₁ a₂ : α} (b : bool) :
  a₁ ≠ a₂ → cond b a₁ a₂ = a₂ → b = ff :=
by cases b; simp [imp_false]

theorem cond_tt_of_not_cond_eq_second_of_ne [decidable_eq α] {a₁ a₂ : α} (b : bool) :
  a₁ ≠ a₂ → ¬(cond b a₁ a₂ = a₂) → b = tt :=
by cases b; simp

theorem cond_ff_of_not_cond_eq_first_of_ne [decidable_eq α] {a₁ a₂ : α} (b : bool) :
  a₂ ≠ a₁ → ¬(cond b a₁ a₂ = a₁) → b = ff :=
by cases b; simp

theorem ne_tail_of_eq_head_of_ne [decidable_eq α] {a b : α} : ∀ {l₁ : list α},
  ∀ {l₂ : list α}, (a :: l₁) ≠ (b :: l₂) → a = b → l₁ ≠ l₂
| []        := by simp
| (x :: xs) := begin
  intros l₂ hneq heq,
  by_contradiction,
  exact absurd (congr (congr_arg cons heq) h) hneq
end

-- Some facts about map that help
theorem exists_of_map_singleton {f : α → β} {b : β} :
  ∀ {l : list α}, map f l = [b] → ∃ a, [a] = l ∧ f a = b
| []        := by { contradiction }
| [x]       := by { simp [map_cons] }
| (x :: y :: ys) := by { simp }

theorem exists_cons_of_map_cons {f : α → β} {b : β} {bs : list β} :
  ∀ {l : list α}, map f l = b :: bs → ∃ h L, l = h :: L ∧ f h = b ∧ map f L = bs
| []        := by { contradiction }
| (x :: xs) := begin 
  simp [map_cons],
  intros hx hxs,
  use x, use xs, simp [hx, hxs]
end

-- If instead the list from above is a map construction too
theorem exists_map_cons_of_map_cons {f : α → β} {a : α} {as : list α} :
  ∀ {l : list α}, map f l = map f (a :: as) → ∃ h L, l = h :: L ∧ f h = f a ∧ map f L = map f as
| []        := by { contradiction }
| (x :: xs) := begin
  simp [map_cons],
  intros hx hxs,
  use [x, xs], simp [hx, hxs]
end

theorem mem_map_append {l₁ l₂ : list α} {f : α → β} {b : β} :
  b ∈ map f (l₁ ++ l₂) → b ∈ map f l₁ ∨ b ∈ map f l₂ :=
by simp

-- Or facts about filter
theorem length_filter {p : α → Prop} [decidable_pred p] {l : list α} : 
  length (filter p l) ≤ length l :=
begin
  induction l with x xs ih,
  { simp },
  { by_cases p x,
    { simp [filter_cons_of_pos _ h, ih] },
    { simp [filter_cons_of_neg _ h, ih, le_add_right] } }
end

-- Sublists need membership theorems, too
theorem mem_of_mem_sublist {l₁ l₂ : list α} {a : α} :
  a ∈ l₁ → l₁ <+ l₂ → a ∈ l₂ :=
assume ha hl, sublist.subset hl ha

theorem not_mem_of_sublist_of_not_mem {l₁ l₂ : list α} {a : α} :
  a ∉ l₂ → l₁ <+ l₂ → a ∉ l₁ :=
assume ha hl h, absurd ((sublist.subset hl) h) ha

-- Very sad theorems on nats
def max_nat : list nat → nat
| []        := 0
| (n :: ns) := max n (max_nat ns)

theorem max_nat_is_max (l : list nat) : ∀ (n : nat), n ∈ l → n ≤ max_nat l :=
begin
  induction l with m ms ih,
  { simp },
  { intros n hn,
    rcases eq_or_mem_of_mem_cons hn with rfl | hms,
    { simp [max_nat] },
    { simp [ih n hms, max_nat] } }
end

theorem not_mem_of_gt_max_nat {l : list nat} {n : nat} : n > max_nat l → n ∉ l :=
begin
  contrapose, simp, exact max_nat_is_max l n
end

theorem not_mem_of_gt_max {l : list nat} {n : nat} : n > foldr max 0 l → n ∉ l :=
begin
  induction l with m ms ih,
  { simp },
  { simp,
    intros hm hn,
    exact not_or_distrib.mpr (and.intro (ne_of_gt hm) (ih hn)) }
end

theorem exists_not_mem_of_gt_max {f : α → nat} (hf : bijective f) {l : list α} :
  ∀ {n : nat}, n > foldr max 0 (map f l) → ∃ (a : α), f a = n ∧ a ∉ l :=
begin
  intros n hn,
  rcases (bijective_iff_exists_unique f).mp hf n with ⟨b, hb, _⟩,
  use b,
  split,
  { simp [hb] },
  { have := not_mem_of_gt_max hn,
    revert this,
    contrapose,
    simp,
    intro h,
    use [b, h, hb] }
end

-- A simple nat result - can be tightened up, but how?
theorem ne_of_add_eq_of_gt_zero {a b c : nat} : a > 0 → a + b = c → b ≠ c :=
begin
  intros ha habc hbc,
  rw hbc at habc,
  have : a + c > c, from lt_add_of_pos_left c ha,
  rw habc at this,
  exact nat.lt_asymm this this,
end

-- Maximum values that map to general α
theorem infimum_gt_list {f : nat → α} (f_inj : injective f) (l : list α) :
  ∃ (n : nat), ∀ (m : nat), m ≥ n → f m ∉ l :=
begin
  induction l with a as ih,
  { simp [not_mem_nil] },
  { rcases ih with ⟨n, hn⟩,
    by_cases h : ∃ (b : nat), f b = a,
    { rcases h with ⟨b, hb⟩,
      by_cases hnb : n > b,
      { use n, 
        intros m hm,
        apply not_mem_cons_of_ne_of_not_mem,
        { rw ← hb,
          exact (injective.ne_iff f_inj).mpr (ne_of_gt (gt_of_ge_of_gt hm hnb)) },
        { exact hn m hm } },
      { use b + 1,
        intros m hm,
        simp at hnb,
        apply not_mem_cons_of_ne_of_not_mem,
        { rw ← hb,
          exact (injective.ne_iff f_inj).mpr (ne_of_gt (nat.succ_le_iff.mp hm)) },
        { exact hn m (le_trans hnb (nat.le_of_succ_le hm)) } } },
    { simp at h,
      use n,
      intros m hm,
      apply not_mem_cons_of_ne_of_not_mem,
      { exact h m },
      { exact hn m hm } } }
end

@[simp] theorem nil_inter [decidable_eq α] (l : list α) : l ∩ [] = [] :=
eq_nil_of_subset_nil (inter_subset_right l [])

theorem zero_left_of_add_zero {n m : nat} : 0 = n + m → n = 0 :=
begin
  cases m,
  { rw add_zero n, intro h, exact h.symm },
  { intro h, linarith }
end

theorem zero_right_of_add_zero {n m : nat} : 0 = n + m → m = 0 :=
begin
  cases n,
  { rw zero_add m, intro h, exact h.symm },
  { intro h, linarith }
end

theorem mem_fst_map_of_mem {l : list (α × β)} {a : α} {b : β} :
  (a, b) ∈ l → a ∈ map prod.fst l :=
begin
  intro h,
  apply mem_map.mpr,
  use [(a, b), h]
end

theorem mem_snd_map_of_mem {l : list (α × β)} {a : α} {b : β} :
  (a, b) ∈ l → b ∈ map prod.snd l :=
begin
  intro h,
  apply mem_map.mpr,
  use [(a, b), h]
end

theorem length_lt_length_cons (a : α) (l : list α) :
  length l < length (a :: l) :=
by simp [length]

theorem strong_induction_on_lists [inhabited α] {p : list α → Prop} (l : list α)
  (h : ∀ l₁, (∀ l₂, length l₂ < length l₁ → p l₂) → p l₁) : p l :=
suffices ∀ (l₁ : list α) (l₂ : list α), length l₂ < length l₁ → p l₂,
  from this ((arbitrary α) :: l) l (length_lt_length_cons (arbitrary α) l),
begin
  intro l₁, induction l₁ with a as ih,
  { intros l₂ h₁, unfold length at h₁, exact absurd h₁ (l₂.length).not_lt_zero },
  { intros m h₁,
    unfold length at h₁,
    apply or.by_cases (decidable.lt_or_eq_of_le (nat.le_of_lt_succ h₁)),
    { intros, apply ih, assumption },
    { intro hlen, have := h m, rw hlen at this, exact this ih } }
end