/-

  This file contains the definitions of and basic operations on variables, literals,
  clauses, and conjunctive normal form.

  Authors: Cayden Codel, Jeremy Avigad, Marijn Heule
  Carnegie Mellon University

-/

import data.multiset.basic
import data.multiset.finset_ops
import data.finset.basic
import data.finset.powerset
import init.data.nat
import init.data.nat.lemmas
import logic.basic
import basic

open decidable

lemma split_two_pow_succ (n : nat) : 2 ^ (n + 1) = 2 ^ n + 2 ^ n :=
begin
  induction n with d hd,
  simp,
  calc 2 ^ (d.succ + 1) = 2 ^ (d.succ + 1) : rfl
                    ... = 2 * 2 ^ (d.succ) : by { rw pow_succ _ _ }
                    ... = 2 ^ (d + 1) + 2 ^ (d + 1) : by { rw nat.succ_mul _ _, simp }
                    ... = 2 ^ (d.succ) + 2 ^ (d.succ) : by { simp }
end

lemma unequal_sets_exi {α : Type} {s₁ s₂ : finset α} : (∃ a, a ∈ s₁ ∧ a ∉ s₂) → s₁ ≠ s₂ :=
begin
  intro h,
  cases h with a ha,
  cases ha with ha1 ha2,
  have z : s₁ = s₂ → ∀ a, a ∈ s₁ ↔ a ∈ s₂, from finset.ext_iff.1,
  cases classical.em (s₁ = s₂),
  have z2 := z h a,
  have z3 := z2.1 ha1,
  exfalso,
  exact ha2 z3,
  exact h,
end

-- These are basically the same -- lemma to transform [inhabited] universal to existential?
lemma unequal_sets {α : Type} [inhabited α] {s₁ s₂ : finset α} {a : α} : a ∈ s₁ ∧ a ∉ s₂ → s₁ ≠ s₂ :=
begin
  intro h,
  cases h with ha hb,
  have z : s₁ = s₂ → ∀ a, a ∈ s₁ ↔ a ∈ s₂, from finset.ext_iff.1,
  cases (classical.em) (s₁ = s₂),
  have z2 := z h a,
  have z3 := z2.1 ha,
  exfalso,
  exact hb z3,
  exact h,
end

/- 
  All propositional formulas are comprised of Boolean variables.
  Here, we represent variables as natural numbers, which may then be evaluated
  with an appropriate assignment of boolean values to those variables.

  Literals are positive and negative instances of those variables.
-/

inductive literal : Type
  | Pos : nat → literal
  | Neg : nat → literal

/- Assignments give boolean values to the variables -/
def assignment := nat → bool

namespace literal

instance : inhabited literal := ⟨Pos 0⟩

instance has_decidable_eq : decidable_eq literal
  | (Pos n) (Pos m) :=
    match nat.decidable_eq n m with
      | is_true hnm   := is_true (hnm ▸ eq.refl (Pos n))
      | is_false hneq := is_false (λ h, literal.no_confusion h (λ habs, absurd habs hneq))
    end
  | (Pos _) (Neg _) := is_false (λ h, literal.no_confusion h)
  | (Neg _) (Pos _) := is_false (λ h, literal.no_confusion h)
  | (Neg n) (Neg m) :=
    match nat.decidable_eq n m with
      | is_true hnm   := is_true (hnm ▸ eq.refl (Neg n))
      | is_false hneq := is_false (λ h, literal.no_confusion h (λ habs, absurd habs hneq))
    end

-- TODO what is the canonical way to prove this, other than simp?
@[simp] lemma diff_parity_neq (n : nat) : Pos n ≠ Neg n :=
begin
  simp,
end

/- Negated literals receive the opposite boolean value as the variable -/
def eval (α : assignment) : literal → bool
  | (Pos n) := α n
  | (Neg n) := bnot (α n)

/- Extracts the natural number boolean variable of the literal -/
def var : literal → nat
  | (Pos n) := n
  | (Neg n) := n

def flip : literal → literal
  | (Pos n) := Neg n
  | (Neg n) := Pos n

def set_pos : literal → literal
  | (Pos n) := Pos n
  | (Neg n) := Pos n

def set_neg : literal → literal
  | (Pos n) := Neg n
  | (Neg n) := Neg n

def is_pos : literal → bool
  | (Pos _) := tt
  | (Neg _) := ff

def is_neg : literal → bool
  | (Pos _) := ff
  | (Neg _) := tt

end literal

/- (Disjunctive) clauses are finite sets of literals.
  The finite set represents the literals joined by logical ORs.
  -/
def clause := finset literal

namespace clause

instance : has_mem literal clause := ⟨λ l c, l ∈ c.1⟩

-- TODO why is the mem_def and has_mem theorems/instance features required?
theorem mem_def {l : literal} {c : clause} : l ∈ c ↔ l ∈ c.1 := iff.rfl

instance : has_emptyc (clause) := ⟨finset.empty⟩

-- Define some equality
--instance has_decidable_eq : decidable_eq clause := sorry

instance : has_union (clause) := ⟨λ c₁ c₂, ⟨_, multiset.nodup_ndunion c₁.1 c₂.2⟩⟩

instance : has_singleton literal clause := ⟨λ l, ⟨{l}, list.nodup_singleton l⟩⟩ 

instance : has_insert literal clause := ⟨λ l c, ⟨_, multiset.nodup_ndinsert l c.2⟩⟩

theorem insert_def (l : literal) (c : clause) : insert l c = ⟨_, multiset.nodup_ndinsert l c.2⟩ := rfl

def erase (c : clause) (l : literal) : clause := ⟨_, multiset.nodup_erase_of_nodup l c.2⟩

/- The clause represents a disjunction, so we evaluate literals until tt is found -/
def eval (α : assignment) (c : clause) : bool :=
  cond (c.card > 0) (cond (∃ l ∈ c, literal.eval α l = tt) tt ff) ff

/- Counts the number of literals that evaluate to true in the clause, under some assignment -/
def count_tt (α : assignment) (c : clause) : nat :=
  finset.card $ c.filter (λ l, l.eval α = tt)

/- Counts the number of literals that evaluate to false in the clause, under some assignment -/
def count_ff (α : assignment) (c : clause) : nat :=
  finset.card $ c.filter (λ l, l.eval α = ff)

/- Counts the number of positive literals in the clause -/
/- TODO why can't I use a match statement? Requires decidable_pred... -/
def count_pos (c : clause) : nat :=
  --list.length $ c.filter (λ l, match l with | (literal.Pos _) := true | _ := false end)
  finset.card $ c.filter (λ l, literal.is_pos l = tt)

/- Counts the number of negative literals in the clause -/
def count_neg (c : clause) : nat :=
  finset.card $ c.filter (λ l, literal.is_neg l = tt)

/- Some useful statements for proofs of clauses -/
lemma empty_eval_ff {α : assignment} {c : clause} : c.card = 0 → eval α c = ff :=
begin
  -- This proof is very similar to the one for lists (change card to length)
  intro h,
  rw finset.card_eq_zero at h,
  rw h,
  unfold eval,
  simp,
end

-- TODO not sure whether to have this be forall or exists...
lemma single_eval_lit [inhabited literal] {α : assignment} {c : clause} : c.card = 1 → ∀ l ∈ c, eval α c = literal.eval α l :=
begin
  intros h l hin,
  rw finset.card_eq_one at h,
  cases h with a ha,
  rw ha at hin,
  have : l = a, from finset.mem_singleton.mp hin,
  rw this,
  rw ha,
  unfold eval,
  simp,
end

end clause

/- Conjunctive normal form is a list of clauses joined by logical ANDs -/
def cnf := finset clause

namespace cnf

instance : has_mem clause cnf := ⟨λ c f, c ∈ f.1⟩

-- TODO why is the mem_def and has_mem theorems/instance features required?
theorem mem_def {c : clause} {f : cnf} : c ∈ f ↔ c ∈ f.1 := iff.rfl

/- The clauses of the CNF are joined by conjunctions, so all must evaluate to true -/
/- The non-list representation does not allow for short circuiting via foldr, but alas... -/
def eval (α : assignment) (f : cnf) : bool :=
  cond (∃ c ∈ f, bnot (clause.eval α c)) ff tt

/- Counts the number of clauses which evaluate to true under some assignment -/
def count_tt (α : assignment) (f : cnf) : nat :=
  finset.card $ f.filter (λ c, c.eval α = tt)

/- Counts the number of clauses which evaluate to false under some assignment -/
def count_ff (α : assignment) (f : cnf) : nat :=
  finset.card $ f.filter (λ c, c.eval α = ff)

/- Some useful simplifying statements -/
lemma empty_eval_ff {α : assignment} {f : cnf} : f.card = 0 → f.eval α = tt :=
begin
  intro h,
  rw finset.card_eq_zero at h,
  rw h,
  unfold eval,
  simp,
end

-- Note: These proofs are identical to the ones above: simpler proof?
lemma single_eval_clause [inhabited clause] {α : assignment} {f : cnf} : f.card = 1 → ∀ c ∈ f, eval α f = clause.eval α c :=
begin
  intros h c hin,
  rw finset.card_eq_one at h,
  cases h with a ha,
  rw ha at hin,
  have : c = a, from finset.mem_singleton.mp hin,
  rw this,
  rw ha,
  unfold eval,
  simp,
end

end cnf

/- Sometimes, it is necessary to get all possible disjunctive clauses from a set of variables -/
/- For lack of a better name, we call that operation "exploding" -/
namespace explode

open literal
open clause

-- NOTE: The above two are the "pure" versions of the functions. However, to prove
-- injectivity, we can sus it by using a bijective verion, even if the second case is never seen
def bij_pos (n : nat) (c : clause) : clause := cond ((Pos n) ∈ c) (erase c (Pos n)) (insert (Pos n) c)

def bij_neg (n : nat) (c : clause) : clause := cond ((Neg n) ∈ c) (erase c (Neg n)) (insert (Neg n) c)

-- TODO there has *got* to be a way to reduce the size of this proof. It's practically trivial...
lemma bij_pos_is_inj (n : nat) (s : set clause) : set.inj_on (bij_pos n) s :=
begin
  intros c₁ c₁_in_s c₂ c₂_in_s bij_pos_eq,
  unfold bij_pos at bij_pos_eq,
  have one_in_or_not : (Pos n) ∈ c₁ ∨ (Pos n) ∉ c₁, from classical.em _,
  have two_in_or_not : (Pos n) ∈ c₂ ∨ (Pos n) ∉ c₂, from classical.em _,

  -- Case 1
  cases one_in_or_not,
  cases two_in_or_not,
  simp [one_in_or_not, two_in_or_not, bool.cond_ff] at bij_pos_eq,
  have one_insert : insert (Pos n) (erase c₁ (Pos n)) = c₁, from finset.insert_erase one_in_or_not,
  have two_insert : insert (Pos n) (erase c₂ (Pos n)) = c₂, from finset.insert_erase two_in_or_not,
  have eq_super : insert (Pos n) (c₁.erase (Pos n)) = insert (Pos n) (c₂.erase (Pos n)), from congr_arg (insert (Pos n)) bij_pos_eq, 
  rw one_insert at eq_super,
  rw two_insert at eq_super,
  exact eq_super,

  -- Case 2
  simp [one_in_or_not, two_in_or_not, bool.cond_ff, bool.cond_tt] at bij_pos_eq,
  exfalso,

  have in_after_insert : (Pos n) ∈ insert (Pos n) c₂, from finset.mem_insert_self _ _,
  have nin_after_erase : (Pos n) ∉ erase c₁ (Pos n), from finset.not_mem_erase _ _,
  have both := and.intro in_after_insert nin_after_erase,
  have uneq : insert (Pos n) c₂ ≠ c₁.erase (Pos n), from unequal_sets both,
  exact uneq bij_pos_eq.symm,

  -- Case 3
  cases two_in_or_not,
  simp [one_in_or_not, two_in_or_not] at bij_pos_eq,
  exfalso,

  have in_after_insert : (Pos n) ∈ insert (Pos n) c₁, from finset.mem_insert_self _ _,
  have nin_after_erase : (Pos n) ∉ erase c₂ (Pos n), from finset.not_mem_erase _ _,
  have both := and.intro in_after_insert nin_after_erase,
  have uneq : insert (Pos n) c₁ ≠ c₂.erase (Pos n), from unequal_sets both,
  exact uneq bij_pos_eq,

  -- Case 4
  simp [one_in_or_not, two_in_or_not] at bij_pos_eq,
  have one_erase : erase (insert (Pos n) c₁) (Pos n) = c₁, from finset.erase_insert one_in_or_not,
  have two_erase : erase (insert (Pos n) c₂) (Pos n) = c₂, from finset.erase_insert two_in_or_not,
  have eq_super : erase (insert (Pos n) c₁) (Pos n) = erase (insert (Pos n) c₂) (Pos n), from congr_arg (λ c, erase c (Pos n)) bij_pos_eq, 
  rw one_erase at eq_super,
  rw two_erase at eq_super,
  exact eq_super,
end

lemma bij_neg_is_inj (n : nat) (s : set clause) : set.inj_on (bij_neg n) s :=
begin
  intros c₁ c₁_in_s c₂ c₂_in_s bij_neg_eq,
  unfold bij_neg at bij_neg_eq,
  have one_in_or_not : (Neg n) ∈ c₁ ∨ (Neg n) ∉ c₁, from classical.em _,
  have two_in_or_not : (Neg n) ∈ c₂ ∨ (Neg n) ∉ c₂, from classical.em _,

  -- Case 1
  cases one_in_or_not,
  cases two_in_or_not,
  simp [one_in_or_not, two_in_or_not, bool.cond_ff] at bij_neg_eq,
  have one_insert : insert (Neg n) (erase c₁ (Neg n)) = c₁, from finset.insert_erase one_in_or_not,
  have two_insert : insert (Neg n) (erase c₂ (Neg n)) = c₂, from finset.insert_erase two_in_or_not,
  have eq_super : insert (Neg n) (c₁.erase (Neg n)) = insert (Neg n) (c₂.erase (Neg n)), from congr_arg (insert (Neg n)) bij_neg_eq, 
  rw one_insert at eq_super,
  rw two_insert at eq_super,
  exact eq_super,

  -- Case 2
  simp [one_in_or_not, two_in_or_not, bool.cond_ff, bool.cond_tt] at bij_neg_eq,
  exfalso,

  have in_after_insert : (Neg n) ∈ insert (Neg n) c₂, from finset.mem_insert_self _ _,
  have nin_after_erase : (Neg n) ∉ erase c₁ (Neg n), from finset.not_mem_erase _ _,
  have both := and.intro in_after_insert nin_after_erase,
  have uneq : insert (Neg n) c₂ ≠ c₁.erase (Neg n), from unequal_sets both,
  exact uneq bij_neg_eq.symm,

  -- Case 3
  cases two_in_or_not,
  simp [one_in_or_not, two_in_or_not] at bij_neg_eq,
  exfalso,

  have in_after_insert : (Neg n) ∈ insert (Neg n) c₁, from finset.mem_insert_self _ _,
  have nin_after_erase : (Neg n) ∉ erase c₂ (Neg n), from finset.not_mem_erase _ _,
  have both := and.intro in_after_insert nin_after_erase,
  have uneq : insert (Neg n) c₁ ≠ c₂.erase (Neg n), from unequal_sets both,
  exact uneq bij_neg_eq,

  -- Case 4
  simp [one_in_or_not, two_in_or_not] at bij_neg_eq,
  have one_erase : erase (insert (Neg n) c₁) (Neg n) = c₁, from finset.erase_insert one_in_or_not,
  have two_erase : erase (insert (Neg n) c₂) (Neg n) = c₂, from finset.erase_insert two_in_or_not,
  have eq_super : erase (insert (Neg n) c₁) (Neg n) = erase (insert (Neg n) c₂) (Neg n), from congr_arg (λ c, erase c (Neg n)) bij_neg_eq, 
  rw one_erase at eq_super,
  rw two_erase at eq_super,
  exact eq_super,
end


-- TODO can refactor to be based on powerset instead
-- TODO consider this as a list or a finset as input
-- Note: On first try, res.image was res.map, but ran into verification problems of injection
def expl : list nat → finset clause
  | []        := ∅
  | [n]       := {{Pos n}, {Neg n}}
  | (n :: ns) := 
    --let
    --  res := expl ns
    --in
    -- Replace two invocations of expl ns with res to "simplify"
      -- Why must I have "open clause" about 10 lines above to write insert?
    (expl ns).image (bij_pos n) ∪ (expl ns).image (bij_neg n)

def expl_correct : list nat → finset clause
  | []        := ∅
  | [n]       := {{Pos n}, {Neg n}}
  | (n :: ns) := (expl ns).image (insert (Pos n)) ∪ (expl ns).image (insert (Neg n))

-- This version uses natural numbers to ensure non-duplication, etc.
-- Generates all sets with literals between 1 and n inclusive
def expl_nat : nat → finset clause
  | 0       := ∅
  | 1       := {{Pos 1}, {Neg 1}}
  | (n + 1) := (expl_nat n).image (insert (Pos (n + 1))) ∪ (expl_nat n).image (insert (Neg (n + 1)))

lemma thing {n m : nat} (h1 : m < n) (h2 : n ≤ m + 1) : n = m + 1 :=
begin
  have h3 : m + 1 ≤ n, from nat.lt_of_succ_le h1,
  exact le_antisymm h2 h3,
end

lemma thing2 {n : nat} (h : 0 < n) : n = (n - 1) + 1 :=
begin
  induction n with d hd,
  exfalso,
  finish,
  simp,
end

lemma gt_one_is_plus_two {n : nat} (h : 1 < n) : n = (n - 2) + 2 :=
begin
  induction n with d hd,
  exfalso,
  finish,

  cases classical.em (d = 0),
  rw h_1 at h,
  exfalso,
  exact nat.lt_asymm h h,

  cases classical.em (d = 1),
  rw h_2,

  have g_ge_one : d ≥ 1, from nat.lt_succ_iff.mp h,
  have g_gt_one : d > 1, from (ne.symm h_2).le_iff_lt.mp g_ge_one,
  have : d = d - 2 + 2, from hd g_gt_one,
  have : nat.succ (d) = nat.succ (d - 2 + 2), from congr_arg nat.succ this,
  simp [this],
end

-- Note: Mathematically, "total" is an overloaded term, and almost certainly not the correct term here
-- What I mean is that if the element is in any set under f, then it's in the image, no matter the makeup of the parent set set
lemma mem_of_total_image {α β : Type} [decidable_eq β] {f : finset α → finset β} {b : β}
  {s : finset α} {sₐ : finset (finset α)} {sₑ : finset β}
  : (∀ (s : finset α), b ∈ f s) → sₑ ∈ finset.image f sₐ → b ∈ sₑ :=
begin
  intros s_b_in_fs se_in_image,
  simp at se_in_image,
  cases se_in_image,
  cases se_in_image_h,
  rw ← se_in_image_h_right,
  exact s_b_in_fs se_in_image_w,
end

-- The eventual goal is to state only those numbers between 1 and n are involved in an exploded clause
-- Technically, a ↔ relationship with the hm hypothesis holds, but I don't know how to properly express it
lemma not_expl_mem_of_not_mem {n m : nat} {c : clause} {l : literal} (h : n > 0) (hm : m > n) : c ∈ expl_nat n → l ∈ c → m ≠ literal.var l :=
begin
  intros cin lin,
  induction n with d hd,
  exfalso,
  assumption,

  -- Induction step
  -- When n = 1 (d = 0), expl_nat is hard-coded, so we take care of that case first
  cases classical.em (d = 0),
  rw h_1 at cin hm,
  unfold expl_nat at cin,
  rw finset.mem_insert at cin,
  rw finset.mem_singleton at cin,
  cases cin;
  rw cin at lin;
  rw finset.mem_singleton.mp lin;
  unfold var;
  exact ne_of_gt hm,

/-
  rw cin at lin,
  rw finset.mem_singleton.mp lin,
  unfold var,
  exact ne_of_gt hm,
  -/

  -- d > 0 case
  have : d > 0, from pos_iff_ne_zero.mpr h_1,
  have m_gt : m > d, from nat.lt_of_succ_lt hm,

  -- Although induction is promising, it isn't actually the best method (get stuck in IH, see above)
  -- Just have direct proof!
  /-
  cases classical.em (n = 1),
  rw h_1 at cin,
  rw h_1 at hm,
  unfold expl_nat at cin,
  rw finset.mem_insert at cin,
  cases cin,
  rw cin at lin,
  rw finset.mem_singleton at lin,
  rw lin,
  unfold var,
  exact ne_of_gt hm,

  rw finset.mem_singleton at cin,
  rw cin at lin,
  rw finset.mem_singleton at lin,
  rw lin,
  unfold var,
  exact ne_of_gt hm,
  have n_ge_one : n ≥ 1, from nat.succ_le_of_lt h,
  have n_gt_one : n > 1, from (ne.symm h_1).le_iff_lt.mp n_ge_one,
  have n_min_two : n = (n - 2) + 2, from gt_one_is_plus_two n_gt_one, -- nat.sub_add_cancel with 2 ≤ n
  rw n_min_two at cin,
  unfold expl_nat at cin,

  have cor : c ∈ finset.image (insert (Pos ((n - 2).succ + 1))) (expl_nat (n - 2).succ) ∨
         c ∈ finset.image (insert (Neg ((n - 2).succ + 1))) (expl_nat (n - 2).succ),
        from finset.mem_union.mp cin,

  cases cor,
  rw nat.succ_eq_add_one at cin,
  have : 1 + 1 = 2, simp,
  rw nat.add_assoc at cin,
  rw this at cin,
  rw ← gt_one_is_plus_two n_gt_one at cin,
  have : n ≥ 2, from nat.succ_le_iff.mpr n_gt_one,
  
  have pred_gt_zero : 0 < n.pred, from nat.lt_pred_iff.mpr n_gt_one,
  /-have sub_two_plus_one : n - 2 + 1 = n - 1, calc
    n - 2 + 1 = n - 2 + 1 : rfl
          ... = nat.pred (n - 1) + 1 : rfl
          ... = nat.pred (nat.pred (n)) + 1 : rfl
          ... = nat.succ (nat.pred (nat.pred (n))) : rfl
          ... = nat.pred (n) : nat.succ_pred_eq_of_pos pred_gt_zero
          ... = n - 1 : nat.pred_eq_sub_one,-/
  have sub_two_plus_one : n - 2 + 1 = n - 1, from nat.sub_add_cancel np_ge_zero,
  -/
end

-- Reason about finset, define ops in terms of lists?

lemma expl_mem_of_mem {n m : nat} (h : n > 0) (hm : 0 < m ∧ m ≤ n) : ∀ c ∈ (expl_nat n), ∃ l ∈ c, m = literal.var l :=
begin
  intros c cin,
  induction n with d hd,
  exfalso,
  assumption, -- How does assumption work?

  cases classical.em (d = 0),
  rw nat.succ_eq_add_one at cin,
  simp [h_1] at cin,
  unfold expl_nat at cin,

  rw nat.succ_eq_add_one at hm,
  rw h_1 at hm,
  simp at *,
  cases hm with hz hnz,
  rw ← nat.add_zero 1 at hnz,
  rw nat.add_comm at hnz,
  have meq : m = 1, from thing hz hnz,
  cases cin,

  -- Case 1
  use Pos 1,
  rw cin,
  split,
  have : Pos 1 = Pos 1, refl,
  exact finset.mem_singleton.2 this,
  unfold var,
  exact meq,

  -- Case 2
  use Neg 1,
  rw cin,
  split,
  have : Neg 1 = Neg 1, refl,
  exact finset.mem_singleton.2 this,
  unfold var,
  exact meq,

  -- Induction step
  have d_gt_zero : d > 0, from pos_iff_ne_zero.mpr h_1,
  rw nat.succ_eq_add_one at cin,
  rw thing2 d_gt_zero at cin,
  rw nat.add_assoc at cin,
  unfold expl_nat at cin,
  have : (d - 1).succ = d,
    rw nat.succ_eq_add_one,
    rw ← thing2 d_gt_zero,

  rw this at cin,
  cases classical.em (m = d.succ),
  rw finset.mem_union at cin,
  cases cin,

  -- Pos case
  use Pos (d + 1),
  split,
  have insert_taut : ∀ (c : clause), (Pos (d + 1)) ∈ insert (Pos (d + 1)) c, from finset.mem_insert_self (Pos (d + 1)),
  have thing3 := mem_of_total_image insert_taut cin, -- Not quite right here...
  exact thing3,
  exact c, -- Why need an instance of finset literal := clause?

  unfold var,
  exact h_2,

  -- Neg case
  use Neg (d + 1),
  split,
  have insert_taut : ∀ (c : clause), (Neg (d + 1)) ∈ insert (Neg (d + 1)) c, from finset.mem_insert_self (Neg (d + 1)),
  have thing3 := mem_of_total_image insert_taut cin, -- Not quite right here...
  exact thing3,
  exact c, -- Why need an instance of finset literal := clause?

  unfold var,
  exact h_2,

  -- Now that m is not d + 1, can use IH
  cases hm with hml hmr,
  have hmr2 : m < d + 1, from (ne.le_iff_lt h_2).mp hmr,
  have hmr3 : m ≤ d, from nat.le_of_lt_succ hmr2,

  rw finset.mem_union at cin,
  have hd2 : c ∈ expl_nat d → (∃ (l : literal) (H : l ∈ c), m = l.var),
    from hd d_gt_zero (and.intro hml hmr3),
  cases cin,

  have exi_b := finset.mem_image.mp cin,
  cases exi_b,
  cases exi_b_h,

end

lemma card_of_expl (l : list nat) : l.length > 0 → finset.card (expl l) = 2 ^ l.length :=
begin
  intro h,
  induction l,
  simp at h,
  exfalso,
  exact h,

  cases l_tl,
  unfold expl,
  simp,
  dec_trivial,

  -- Induction hypothesis case
  have : (l_tl_hd :: l_tl_tl) ≠ list.nil, from list.cons_ne_nil l_tl_hd l_tl_tl,
  have pos_len : (l_tl_hd :: l_tl_tl).length > 0, from list.length_pos_of_ne_nil this,
  have k := l_ih pos_len,
  unfold expl,
  have pos_eq : finset.card (finset.image (bij_pos l_hd) (expl (l_tl_hd :: l_tl_tl))) = finset.card (expl (l_tl_hd :: l_tl_tl)),
    from finset.card_image_of_inj_on (bij_pos_is_inj l_hd (expl (l_tl_hd :: l_tl_tl))),
  
  have neg_eq : finset.card (finset.image (bij_neg l_hd) (expl (l_tl_hd :: l_tl_tl))) = finset.card (expl (l_tl_hd :: l_tl_tl)),
    from finset.card_image_of_inj_on (bij_neg_is_inj l_hd (expl (l_tl_hd :: l_tl_tl))),

  rw k at pos_eq,
  rw k at neg_eq,

  have goal_eq : finset.card (
    finset.image (bij_pos l_hd) (expl (l_tl_hd :: l_tl_tl)) ∪ 
    finset.image (bij_neg l_hd) (expl (l_tl_hd :: l_tl_tl))) + 
    finset.card (
    finset.image (bij_pos l_hd) (expl (l_tl_hd :: l_tl_tl)) ∩
    finset.image (bij_neg l_hd) (expl (l_tl_hd :: l_tl_tl))) =
    finset.card (finset.image (bij_pos l_hd) (expl (l_tl_hd :: l_tl_tl))) + 
    finset.card (finset.image (bij_neg l_hd) (expl (l_tl_hd :: l_tl_tl))), 
    from finset.card_union_add_card_inter _ _,
  
  rw pos_eq at goal_eq,
  rw neg_eq at goal_eq,
  rw list.length_cons,
  rw split_two_pow_succ,
  have cap_zero : finset.card (finset.image (bij_pos l_hd) (expl (l_tl_hd :: l_tl_tl)) ∩ 
    finset.image (bij_neg l_hd) (expl (l_tl_hd :: l_tl_tl))) = 0, 
    apply finset.card_eq_zero.2,
    apply finset.eq_empty_iff_forall_not_mem.2,
    intro x,
    cases classical.em (x ∈ finset.image (bij_pos l_hd) (expl (l_tl_hd :: l_tl_tl)) ∩ 
    finset.image (bij_neg l_hd) (expl (l_tl_hd :: l_tl_tl))),
      exfalso,
      have h_2 := finset.mem_inter.1 h_1,
      cases h_2 with h_2pos h_2neg,
      sorry,
    sorry,
  sorry,
end

/- True if clause has even number of negated clauses, false otherwise -/
def expl_parity (l : list nat) : list (clause × bool) :=
  l.foldr (λ n, λ r,
    (r.map (λ e, let (cl, par) := e in ⟨(Pos n) :: cl, par⟩) ++ 
    (r.map (λ e, let (cl, par) := e in ⟨(Neg n) :: cl, bnot par⟩)))) [([], tt)]

/- Counts the number of negated literals in each clause -/
def expl_count (l : list nat) : list (clause × nat) :=
  l.foldr (λ n, λ r,
    (r.map (λ e, let (cl, c) := e in ⟨(Pos n) :: cl, c⟩) ++ 
    (r.map (λ e, let (cl, c) := e in ⟨(Neg n) :: cl, c + 1⟩)))) [([], 0)]

-- Again, this proof is exactly the same as the eval single above
lemma explode_single (l : list nat) : l.length = 1 → expl l = [[Pos l.head], [Neg l.head]] :=
begin
  intro h,
  rw list.length_eq_one at h,
  cases h with a ha,
  unfold expl,
  simp [ha],
end

/-
lemma two_card_is_two {α : Type} /-[has_union (finset α)] [has_inter (finset α)]-/ [has_insert α (finset α)] [decidable_eq α] (a b : α) (h : a ≠ b) : ({a, b} : finset α).card = 2 :=
begin
  --unfold finset.card,
  --have carda : finset.card {a} = 1, from finset.card_singleton a,
  have cardb : finset.card {b} = 1, from finset.card_singleton b,
  have anotb : a ∉ {b}, from finset.not_mem_singleton.mpr h,
  --have bnota : b ∉ {a}, from finset.not_mem_singleton.mpr (ne.symm h),
  --have iempt : {a} ∩ {b} = ∅, from finset.inter_singleton_of_not_mem bnota,
  --have dis : disjoint {a} {b}, from finset.disjoint_iff_inter_eq_empty.2 iempt,
  --have dis_un : finset.card ({a} ∪ {b}) = finset.card {a} + finset.card {b}, from finset.card_disjoint_union dis,
  --rw carda at dis_un,
  --rw cardb at dis_un,
  have : finset.card (insert a {b}) = finset.card {b} + 1, from finset.card_insert_of_not_mem anotb, 
  rw cardb at this,
  have simple : 2 = 1 + 1, simp,
  rw simple,
  --exact this, sorry,
  sorry,
end
-/

end explode