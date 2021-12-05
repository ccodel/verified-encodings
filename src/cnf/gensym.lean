/-
Following the tradition of other programming languages,
gensym.lean contains the definition and proofs for a
variable generator for CNF encodings.

Authors: Cayden Codel, Jeremy Avigad, Marijn Heule
Carnegie Mellon University
-/

import cnf.cnf_general
import data.list.basic
import logic.function.basic
import data.nat.basic

open function
open prod
open list

universe u

variable {α : Type u}

/- A gensym is defined by

    - offset: How far along the gensym has assigned variables
    - delta: How much the offset is changed by each assignment
    - f: Convert from nats to desired variable types
    - h: Proof of injectivity, so variable assignments don't conflict

  The update rule is simple: offset + delta.
-/
structure gensym (α : Type u) :=
(offset : nat)
(delta : nat)
(f : nat → α)
(delta_pos : delta > 0) -- Make into subtypes of delta and f?
(f_inj : injective f)

namespace gensym

/-! # Instance properties -/

/- Two gensyms are equal if their component parts agree -/
--@[derive equivalence] <-- This doesn't work - how come?
-- Theorem g₁ = g₂ iff ... below
-- congr_xxx 
protected def eq (g₁ g₂ : gensym α) := g₁.1 = g₂.1 ∧ g₁.2 = g₂.2 ∧ g₁.3 = g₂.3

/-
cases g
g = {offset := g.offset, delta := g.delta, f := g.f }
-/

@[refl] theorem eq.refl (g : gensym α) : g = g := rfl

@[symm] theorem eq.symm {g₁ g₂ : gensym α} (p : g₁ = g₂) : g₂ = g₁ :=
by simp [p]

theorem eq_comm {g₁ g₂ : gensym α} : g₁ = g₂ ↔ g₂ = g₁ :=
⟨eq.symm, eq.symm⟩

@[trans] theorem eq.trans {g₁ g₂ g₃ : gensym α} : g₁ = g₂ → g₂ = g₃ → g₁ = g₃ :=
eq.trans -- This doesn't seem sketchy at all...

/- For some reason, the above doesn't work.... -/
def equiv (g₁ g₂ : gensym α) := g₁.1 = g₂.1 ∧ g₁.3 = g₂.3

notation g₁ ` ≃ ` g₂ := equiv g₁ g₂

@[refl] theorem equiv.refl (g : gensym α) : g ≃ g :=
by simp [equiv]

@[symm] theorem equiv.symm {g₁ g₂ : gensym α} (p : g₁ ≃ g₂) : g₂ ≃ g₁ :=
begin
  unfold equiv at p,
  simp [equiv, p]
end

theorem equiv_comm {g₁ g₂ : gensym α} : g₁ ≃ g₂ ↔ g₂ ≃ g₁ :=
⟨equiv.symm, equiv.symm⟩

@[trans] theorem equiv.trans {g₁ g₂ g₃ : gensym α} : g₁ ≃ g₂ → g₂ ≃ g₃ → g₁ ≃ g₃ :=
begin
  simp [equiv],
  intros ho₁ hf₁ ho₂ hf₂,
  simp [ho₁, hf₁, ho₂, hf₂]
end

theorem equiv_of_eq {g₁ g₂ : gensym α} : g₁ = g₂ → g₁ ≃ g₂ :=
assume h, by simp [h]

/-! # Gensym creation -/

/- Initial gensym that starts at 0 -/
def init {f : nat → α} (f_inj : injective f) : gensym α :=
{ offset := 0, delta := 1, f := f, delta_pos := nat.one_pos, f_inj := f_inj }

/- Given explicit functions between the two types that are inverses of each other,
    we create a gensym object that starts at one more than the maximum of the given list. -/
def seed {f : nat → α} (f_inj : injective f) {g : α → nat} (g_inj : injective g)
  (rinv : right_inverse f g)
 : list α → gensym α
| [] := init f_inj
| l  := { offset := 1 + max_nat (map g l), 
          delta := 1, f := f, delta_pos := nat.one_pos, f_inj := f_inj }

@[simp] theorem seed_nil_eq_init {f : nat → α} (f_inj : injective f) 
  {g : α → nat} (g_inj : injective g) (rinv : right_inverse f g) :
  seed f_inj g_inj rinv [] ≃ init f_inj :=
by simp [seed, init]

/-! ### Fresh variable generation -/

/-! # fresh -/

-- Generates a new variable and returns an updated gensym
def fresh (g : gensym α) : (α × gensym α) :=
⟨g.f (g.offset), ⟨g.offset + g.delta, g.delta, g.f, g.delta_pos, g.f_inj⟩⟩

@[simp] theorem fresh_offset (g : gensym α) :
  (fresh g).2.offset = g.offset + g.delta :=
by simp [fresh]

@[simp] theorem fresh_delta (g : gensym α) : 
  (fresh g).2.delta = g.delta :=
by simp [fresh]

@[simp] theorem fresh_f (g : gensym α) : (fresh g).2.f = g.f :=
by simp [fresh]

theorem fresh_delta_pos (g : gensym α) :
  (fresh g).2.delta > 0 :=
(fresh g).2.delta_pos

theorem fresh_f_injective (g : gensym α) :
  injective (fresh g).2.f :=
(fresh g).2.f_inj

/-! # nfresh -/

/- Generates a list of n new variables and returns the gensym at the end -/
def nfresh : gensym α → nat → (list α × gensym α)
| g 0       := ⟨[], g⟩
| g (n + 1) := let ⟨a, g₂⟩ := fresh g in
               prod.map (λ l, a :: l) id (nfresh g₂ n)

@[simp] theorem nfresh_zero (g : gensym α) : nfresh g 0 = ⟨[], g⟩ := rfl

@[simp] theorem nfresh_one (g : gensym α) : (nfresh g 1).2 = (fresh g).2 :=
by simp [nfresh, fresh]

@[simp] theorem nfresh_offset (g : gensym α) (n : nat) :
  (nfresh g n).2.offset = (g.delta * n) + g.offset :=
begin
  induction n with n ih generalizing g,
  { simp [nfresh] },
  { simp [nfresh, fresh, ih],
    rw [add_comm g.offset g.delta, ← add_assoc, nat.succ_eq_add_one],
    simp [mul_add] }
end

@[simp] theorem nfresh_delta (g : gensym α) (n : nat) : 
  (nfresh g n).2.delta = g.delta :=
begin
  induction n with n ih generalizing g,
  { simp [nfresh] },
  { simp [nfresh, fresh, ih] }
end

@[simp] theorem nfresh_f (g : gensym α) (n : nat) : (nfresh g n).2.f = g.f :=
begin
  induction n with n ih generalizing g,
  { simp [nfresh] },
  { simp [nfresh, fresh, ih] }
end

theorem nfresh_f_injective (g : gensym α) (n : nat) : injective (nfresh g n).2.f :=
(nfresh g n).2.f_inj

theorem nfresh_delta_pos (g : gensym α) (n : nat) : (nfresh g n).2.delta > 0 :=
(nfresh g n).2.delta_pos

theorem nfresh_one_eq_fresh (g : gensym α) : 
  prod.map (λ a, [a]) id (fresh g) = nfresh g 1 :=
by simp [fresh, nfresh]

theorem nfresh_succ_eq_nfresh_fresh (g : gensym α) (n : nat) :
  nfresh g (n + 1) = ⟨(fresh g).1 :: (nfresh (fresh g).2 n).1, (fresh (nfresh g n).2).2⟩ :=
begin
  induction n with n ih generalizing g,
  { simp [nfresh, fresh] },
  { simp [nfresh, fresh, ih, add_assoc] }
end

theorem nfresh_succ_gensym_eq_fresh_nfresh_gensym (g : gensym α) (n : nat) :
  (nfresh g (n + 1)).2 = (fresh (nfresh g n).2).2 :=
by simp [nfresh_succ_eq_nfresh_fresh]

theorem nfresh_succ_gensym_eq_nfresh_fresh_gensym (g : gensym α) (n : nat) :
  (nfresh g (n + 1)).2 = (nfresh (fresh g).2 n).2 :=
by simp [nfresh_succ_eq_nfresh_fresh, nfresh, fresh]

/-
theorem nfresh_succ_eq_nfresh_append_fresh (g : gensym α) (n : nat) :
  nfresh g (n + 1) = ⟨(nfresh g n).1 ++ [(fresh (nfresh g n).2).1], (fresh (nfresh g n).2).2⟩ :=
begin
  induction n with n ih generalizing g,
  { simp [nfresh, fresh] },
  {
    rw nfresh_succ_eq_nfresh_fresh g (n + 1),
    rw ih g.fresh.snd,
    simp,
    rw ih g,
    simp,
  }
end
-/

theorem length_list_nfresh (g : gensym α) (n : nat) : 
  length (nfresh g n).1 = n :=
begin
  induction n with n ih generalizing g,
  { simp [nfresh] },
  { simp [nfresh_succ_eq_nfresh_fresh, ih] }
end

/- nfresh can be split across two calls -/
theorem nfresh_concat (g : gensym α) {n m₁ m₂ : nat} :
  n = m₁ + m₂ → (nfresh g n).2 = (nfresh (nfresh g m₁).2 m₂).2 :=
begin
  induction n with n ih generalizing m₁ m₂,
  { intro h,
    rw zero_left_of_add_zero h,
    rw zero_right_of_add_zero h,
    simp },
  { cases m₂,
    { simp, intro h, simp [h] },
    { intro h,
      rw nat.succ_eq_add_one at h,
      rw nat.succ_eq_add_one at h,
      rw ← add_assoc at h,
      simp [ih (nat.succ.inj h),
        nfresh_succ_gensym_eq_fresh_nfresh_gensym] } }
end

/-
theorem nfresh_concat2 (g : gensym α) {n m₁ m₂ : nat} : n = m₁ + m₂ → 
  (nfresh g n).1 = (nfresh g m₁).1 ++ (nfresh (nfresh g m₁).2 m₂).1 :=
begin
  induction n with n ih generalizing m₁ m₂,
end
-/

def alt_nfresh (g : gensym α) : nat → (list α × gensym α)
| 0       := ⟨[], g⟩
| (n + 1) := ⟨map (λ i, g.f (g.offset + (i) * g.delta)) (range (n + 1)),
             {offset := g.offset + (n + 1) * g.delta,
              delta := g.delta,
              f := g.f,
              delta_pos := g.delta_pos,
              f_inj := g.f_inj }⟩

@[simp] theorem alt_zero (g : gensym α) : alt_nfresh g 0 = ⟨[], g⟩ := rfl

@[simp] theorem alt_one (g : gensym α) : alt_nfresh g 1 = prod.map (λ a, [a]) id (fresh g) :=
by simp [alt_nfresh, fresh, range, range_core]

theorem alt_succ (g : gensym α) (n : nat) :
  alt_nfresh g (n + 1) = ⟨(fresh g).1 :: (alt_nfresh (fresh g).2 n).1, (alt_nfresh (fresh g).2 n).2⟩ :=
begin
  induction n with n ih,
  { simp },
  {
    simp [alt_nfresh, fresh],
    split,
    {
      unfold range,
      unfold range_core,

    },
    { rw nat.succ_eq_add_one, -- Algebra sucky
      repeat { rw add_mul },
      simp,
      repeat { rw add_assoc },
      rw ← add_assoc g.delta (n * g.delta) g.delta,
      rw add_comm g.delta (n * g.delta),
      rw add_assoc (n * g.delta) g.delta g.delta,
      simp
    }
    
  }
end

theorem alt_nfresh_eq_nfresh (g : gensym α) (n : nat) :
  (nfresh g n).1 = (alt_nfresh g n).1 :=
begin
  induction n with n ih generalizing g,
  { simp },
  {

  }
end

/-! # split -/

/- Creates a set of n new gensym objects that are disjoint, in the sense that
   they will not generate any equal terms in future fresh calls. -/
def split (g : gensym α) : nat → list (gensym α)
| 0       := []
| (n + 1) := list.map (λ (e : (nat × gensym α)),
           ⟨e.2.offset + (e.1 * e.2.delta), -- Add delta times the index
            e.2.delta * (n + 1), -- Hilbert-hotel by the input number
            e.2.f,
            mul_pos e.2.delta_pos n.succ_pos,
            e.2.f_inj⟩)
            (enum (repeat g (n + 1)))

@[simp] theorem split_zero (g : gensym α) : split g 0 = [] := rfl

theorem length_split (g : gensym α) (n : nat) :
  length (split g n) = n :=
begin
  cases n,
  { simp },
  { simp [split, length_enum, length_repeat] }
end

/-! # Uniqueness of fresh output -/

/-! # descendant -/

/- If a number of fresh calls can be made to get to a gensym from a first gensym,
    then the second gensym is a descendant of the first -/
-- NOTE: g₂ is a descendant if it can be arrived at via some number of nfresh calls
--       AND g₂'s delta is divided by g₁'s (i.e. a product of some number of split calls)
def descendant (g₁ g₂ : gensym α) := 
  g₁.delta ∣ g₂.delta ∧ ∃ (n : nat), g₂ ≃ (nfresh g₁ n).2

notation g₁ ` ↦ ` g₂ := descendant g₁ g₂

@[refl] theorem descendant.refl (g : gensym α) : g ↦ g :=
and.intro dvd_rfl (exists.intro 0 (by refl))

@[trans] theorem descendant.trans {g₁ g₂ g₃ : gensym α} :
  (g₁ ↦ g₂) → (g₂ ↦ g₃) → (g₁ ↦ g₃) :=
begin
  rintros ⟨hd1, n, ho1, hf1⟩ ⟨hd2, m, ho2, hf2⟩,
  split,
  { exact dvd_trans hd1 hd2 },
  { rcases hd1 with ⟨k1, hk1⟩,
    rw nfresh_offset at ho1,
    rw nfresh_offset at ho2,
    use k1 * m + n,
    split,
    { rw nfresh_offset,
      simp [ho2, ho1, hk1, ← add_assoc, mul_add, mul_assoc] },
    { rw nfresh_f at hf1,
      rw nfresh_f at hf2,
      simp [nfresh_f, hf1, hf2] } }
end

theorem descendant_init (g : gensym α) : init g.f_inj ↦ g :=
begin
  unfold init,
  split,
  { exact one_dvd g.delta },
  { use g.offset,
    split,
    { simp [nfresh_offset _ g.offset] },
    { simp [nfresh_f] } }
end

theorem nfresh_descendant (g : gensym α) (n : nat) : g ↦ (nfresh g n).2 :=
and.intro (by simp [nfresh_offset]) (exists.intro n (by refl))

theorem split_descendant (g : gensym α) (n : nat) : ∀ g₂ ∈ split g n, g ↦ g₂ :=
begin
  cases n,
  { simp },
  { simp [split, -repeat_succ, -repeat],
    rintros g₂ d x hx rfl,
    unfold descendant,
    have := mem_snd_map_of_mem hx,
    rw enum_map_snd at this,
    rw eq_of_mem_repeat this,
    split,
    { simp },
    { use d,
      split,
      { simp [add_comm, mul_comm] },
      { simp } } }
end

/-! # disjoint -/

def disjoint (g₁ g₂ : gensym α) := 
  ((g₁.delta ∣ g₂.delta) ∨ (g₂.delta ∣ g₁.delta)) ∧ (g₁.f = g₂.f) ∧ 
  (∀ (n m : nat), ((nfresh g₁ n).2.offset ≠ (nfresh g₂ m).2.offset))

theorem disjoint.antirefl (g : gensym α) : ¬(disjoint g g) :=
begin
  rintros ⟨_, _, h⟩,
  have := h 0 0,
  contradiction
end

theorem disjoint_comm {g₁ g₂ : gensym α} :
  disjoint g₁ g₂ ↔ disjoint g₂ g₁ :=
begin
  split;
  { rintros ⟨hor, hf, h⟩,
    unfold disjoint,
    split,
    { exact or.comm.mp hor },
    { split,
      { exact hf.symm },
      { intros n m,
        exact ne.symm (h m n) } } }
end

theorem not_disjoint_of_descendant {g₁ g₂ : gensym α} :
  (g₁ ↦ g₂) → ¬(disjoint g₁ g₂) :=
begin
  rintros ⟨_, n, hn⟩ ⟨_, _, h⟩,
  rw equiv_comm at hn,
  have := h n 0,
  rw nfresh_zero at this,
  unfold snd at this,
  exact this (hn.1)
end

theorem not_descendant_of_disjoint {g₁ g₂ : gensym α} :
  disjoint g₁ g₂ → ¬(g₁ ↦ g₂) ∧ ¬(g₂ ↦ g₁) :=
begin
  rintros ⟨_, hf, h⟩,
  split,
  { rintros ⟨_, n, hno, hnf⟩,
    have := ne.symm (h n 0),
    rw nfresh_zero at this,
    unfold snd at this,
    exact this hno },
  { rintros ⟨_, m, hmo, hmf⟩,
    have := h 0 m,
    rw nfresh_zero at this,
    unfold snd at this,
    exact this hmo }
end

theorem disjoint_fresh_of_disjoint {g₁ g₂ : gensym α} :
  disjoint g₁ g₂ → disjoint (fresh g₁).2 g₂ :=
begin
  rintros ⟨hor, hf, h⟩,
  split,
  { rw fresh_delta, exact hor },
  { split, 
    { rw fresh_f, exact hf },
    { intros n m,
      rw ← nfresh_succ_gensym_eq_nfresh_fresh_gensym,
      exact h (n + 1) m } }
end

theorem disjoint_nfresh_of_disjoint {g₁ g₂ : gensym α} (n : nat) :
  disjoint g₁ g₂ → disjoint (nfresh g₁ n).2 g₂ :=
begin
  rintros ⟨hor, hf, h⟩,
  split,
  { rw nfresh_delta, exact hor },
  { split,
    { rw nfresh_f, exact hf },
    { intros x y,
      have : n + x = n + x, from rfl,
      rw ← nfresh_concat g₁ this,
      exact h (n + x) y } }
end

theorem inter_nil_of_disjoint [decidable_eq α] {g₁ g₂ : gensym α} :
  disjoint g₁ g₂ → ∀ (n m : nat), (nfresh g₁ n).1 ∩ (nfresh g₂ m).1 = [] :=
begin
  rintros ⟨hdiv, hf, ho⟩ n m,
  induction n with n ih generalizing g₁,
  { simp },
  {
    rw nfresh_succ_eq_nfresh_fresh,
    unfold fst,
    have hfreshdel : (fresh g₁).2.delta ∣ g₂.delta ∨ g₂.delta ∣ (fresh g₁).2.delta,
    { rw fresh_delta, exact hdiv },
    have hfreshf : (fresh g₁).2.f = g₂.f,
    { rw fresh_f, exact hf },
    have hfresho : ∀ (n m : nat),
      (nfresh (fresh g₁).2 n).2.offset ≠ (nfresh g₂ m).2.offset,
    { intros n m,
      rw ← nfresh_succ_gensym_eq_nfresh_fresh_gensym,
      exact ho (n + 1) m },
    have ihred := ih hfreshdel hfreshf hfresho,
    have : (fresh g₁).1 ∉ (nfresh g₂ m).1,
    {

    }
  }
end

end gensym