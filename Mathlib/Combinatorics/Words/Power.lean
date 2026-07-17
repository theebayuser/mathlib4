/-
Copyright (c) 2026 Daniel Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Liao
-/
module

public import Mathlib.Data.List.PeriodicityLemma

/-!
# Powers and overlaps of words

Combinatorics-on-words repetition predicates on `List α`, generic in the alphabet:

* `List.IsPower r v`: `v` is an `r`-th power — the `r`-fold repetition of a *nonempty*
  root. The nonempty-root requirement is the combinatorics-on-words convention and
  deliberately distinguishes this predicate from the algebraic `IsSquare`/`Monoid.pow`
  notions, for which the identity is a power.
* `List.IsOverlap v`: `v` has the form `a x a x a` — a repetition of exponent greater
  than two (the objects forbidden by Thue's overlap-free theorem).

Main results:

* `List.isPower_iff_hasPeriod`: for `0 < r`, `v` is an `r`-th power iff it has a
  positive period `p` with `v.length = r * p` — connecting the root-decomposition
  form to `List.HasPeriod` (and hence to the Fine–Wilf theorem `List.HasPeriod.gcd`).
* `List.isOverlap_iff_hasPeriod`: `v` is an overlap iff it has a positive period `p`
  with `v.length = 2 * p + 1`.

Both predicates are decidable (with `DecidableEq α`) by bounded period search; for
`IsPower` the instance is stated for positive exponents, since `IsPower 0 v` reduces
to the undecidable-in-general `v = [] ∧ Nonempty α`.

## References

* [M. Lothaire, *Combinatorics on Words*][lothaire1997]
* A. Thue, *Über unendliche Zeichenreihen*, 1906.

## Tags

combinatorics on words, power, square, overlap, repetition, period
-/

@[expose] public section

namespace List

variable {α : Type*}

/-! ### Powers -/

/-- `v` is an `r`-th power: the `r`-fold repetition of a nonempty root. -/
def IsPower (r : ℕ) (v : List α) : Prop :=
  ∃ u : List α, u ≠ [] ∧ v = (replicate r u).flatten

/-- The `r`-fold repetition of a nonempty root is an `r`-th power. -/
theorem isPower_flatten_replicate {r : ℕ} {u : List α} (hu : u ≠ []) :
    IsPower r ((replicate r u).flatten) := ⟨u, hu, rfl⟩

/-- An `r`-th power with positive exponent is nonempty (the root is nonempty). -/
theorem IsPower.length_pos {r : ℕ} (hr : 0 < r) {v : List α} (h : IsPower r v) :
    0 < v.length := by
  obtain ⟨u, hu, rfl⟩ := h
  rw [length_flatten_replicate]
  exact Nat.mul_pos hr (length_pos_of_ne_nil hu)

/-- A word is an `r`-th power (`0 < r`) iff it has a positive period `p` and length
exactly `r * p`. Connects the root-decomposition form of powers with `List.HasPeriod`. -/
theorem isPower_iff_hasPeriod {r : ℕ} (hr : 0 < r) {v : List α} :
    IsPower r v ↔ ∃ p, 0 < p ∧ v.length = r * p ∧ v.HasPeriod p := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u.length, length_pos_of_ne_nil hu, length_flatten_replicate r u,
      hasPeriod_flatten_replicate r u⟩
  · rintro ⟨p, hp, hlen, per⟩
    have hple : p ≤ v.length := by
      rw [hlen]; exact Nat.le_mul_of_pos_left p hr
    refine ⟨v.take p, ?_, eq_flatten_replicate_of_hasPeriod per hlen⟩
    have htk : (v.take p).length = p := by
      rw [length_take, min_eq_left hple]
    exact ne_nil_of_length_pos (by rw [htk]; exact hp)

/-- Squares are `2`-powers in the concatenation form. -/
theorem isPower_two_iff {v : List α} :
    IsPower 2 v ↔ ∃ u, u ≠ [] ∧ v = u ++ u := by
  have h2 : ∀ u : List α, (replicate 2 u).flatten = u ++ u := by
    intro u
    have hrep : replicate 2 u = [u, u] := rfl
    rw [hrep]; simp
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, h2 u⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, (h2 u).symm⟩

/-- Bounded-search form of `isPower_iff_hasPeriod`: candidate periods are below the
length. Gives decidability. -/
theorem isPower_iff_bounded {r : ℕ} (hr : 0 < r) {v : List α} :
    IsPower r v ↔
      ∃ p ∈ range (v.length + 1), 0 < p ∧ v.length = r * p ∧ v.HasPeriod p := by
  rw [isPower_iff_hasPeriod hr]
  constructor
  · rintro ⟨p, hp, hlen, per⟩
    have hple : p ≤ v.length := by
      rw [hlen]; exact Nat.le_mul_of_pos_left p hr
    exact ⟨p, mem_range.mpr (by omega), hp, hlen, per⟩
  · rintro ⟨p, _, hp, hlen, per⟩
    exact ⟨p, hp, hlen, per⟩

instance [DecidableEq α] (r : ℕ) (v : List α) : Decidable (IsPower (r + 1) v) :=
  decidable_of_iff _ (isPower_iff_bounded (Nat.succ_pos r)).symm

/-! ### Overlaps -/

/-- `v` is an *overlap*: a word of the form `a x a x a` (single letter `a`, word `x`) —
a repetition of exponent strictly greater than `2`. The smallest overlaps are `aaa`
(`x = []`) and `ababa` (`x = [b]`). -/
def IsOverlap (v : List α) : Prop :=
  ∃ (a : α) (x : List α), v = [a] ++ x ++ [a] ++ x ++ [a]

/-- An overlap `a x a x a` has period `|x| + 1` (it is a prefix of `(a x)³`) and odd
length `2 (|x| + 1) + 1`. -/
theorem IsOverlap.hasPeriod {v : List α} (h : IsOverlap v) :
    ∃ p, 0 < p ∧ v.length = 2 * p + 1 ∧ v.HasPeriod p := by
  obtain ⟨a, x, rfl⟩ := h
  refine ⟨x.length + 1, Nat.succ_pos _, by simp; omega, ?_⟩
  have hinfix : [a] ++ x ++ [a] ++ x ++ [a] <:+: (replicate 3 ([a] ++ x)).flatten := by
    refine ⟨[], x, ?_⟩
    have hrep : replicate 3 ([a] ++ x) = [[a] ++ x, [a] ++ x, [a] ++ x] := rfl
    rw [hrep]
    simp [append_assoc]
  have hper := (hasPeriod_flatten_replicate 3 ([a] ++ x)).infix hinfix
  have hlen1 : ([a] ++ x).length = x.length + 1 := by simp
  rwa [hlen1] at hper

/-- A word with a positive period `p` and length `2 * p + 1` is an overlap. -/
theorem isOverlap_of_hasPeriod {v : List α} {p : ℕ} (hp : 0 < p)
    (hlen : v.length = 2 * p + 1) (per : v.HasPeriod p) : IsOverlap v := by
  have h2p : 2 * p < v.length := by omega
  -- the copy at offset `p` agrees with the length-`p` prefix
  have hcopy : (v.drop p).take p = v.take p := by
    have hp_le : p ≤ (v.drop p).length := by rw [length_drop]; omega
    rw [prefix_iff_eq_take.mp (per.drop_prefix p), take_take, min_eq_left hp_le]
  -- the last letter agrees with the first
  have hlast : v[2 * p]? = v[0]? := by
    have h1 := hasPeriod_iff_getElem?.mp per 0 (by omega)
    have h2 := hasPeriod_iff_getElem?.mp per p (by omega)
    rw [Nat.zero_add] at h1
    have hpp : p + p = 2 * p := by omega
    rw [hpp] at h2
    rw [← h2, ← h1]
  -- split `v` into prefix, copy, and final letter
  have hsplit : v = v.take p ++ (v.drop p).take p ++ [v[2 * p]] := by
    have hdrop2 : v.drop (2 * p) = [v[2 * p]] := by
      rw [drop_eq_getElem_cons h2p, drop_eq_nil_of_le (by omega)]
    calc v = v.take (2 * p) ++ v.drop (2 * p) := (take_append_drop _ v).symm
      _ = (v.take p ++ (v.drop p).take p) ++ v.drop (2 * p) := by
          rw [Nat.two_mul, take_add]
      _ = v.take p ++ (v.drop p).take p ++ [v[2 * p]] := by rw [hdrop2]
  -- peel the first letter off the root
  have htne : v.take p ≠ [] := by
    have htk : (v.take p).length = p := by
      rw [length_take, min_eq_left (by omega)]
    exact ne_nil_of_length_pos (by rw [htk]; exact hp)
  obtain ⟨b, t, hbt⟩ := exists_cons_of_ne_nil htne
  have hb : v[0]? = some b := by
    have h0 : (v.take p)[0]? = v[0]? := getElem?_take_of_lt hp
    rw [← h0, hbt]
    rfl
  have hlastb : v[2 * p] = b := by
    have hsome := hlast.trans hb
    rw [getElem?_eq_getElem h2p] at hsome
    exact Option.some_inj.mp hsome
  refine ⟨b, t, ?_⟩
  calc v = v.take p ++ (v.drop p).take p ++ [v[2 * p]] := hsplit
    _ = (b :: t) ++ (b :: t) ++ [b] := by rw [hcopy, hbt, hlastb]
    _ = [b] ++ t ++ [b] ++ t ++ [b] := by simp [append_assoc]

/-- A word is an overlap iff it has a positive period `p` and length `2 * p + 1`. -/
theorem isOverlap_iff_hasPeriod {v : List α} :
    IsOverlap v ↔ ∃ p, 0 < p ∧ v.length = 2 * p + 1 ∧ v.HasPeriod p :=
  ⟨IsOverlap.hasPeriod, fun ⟨_, hp, hlen, per⟩ => isOverlap_of_hasPeriod hp hlen per⟩

/-- Bounded-search form of `isOverlap_iff_hasPeriod`. Gives decidability. -/
theorem isOverlap_iff_bounded {v : List α} :
    IsOverlap v ↔
      ∃ p ∈ range v.length, 0 < p ∧ v.length = 2 * p + 1 ∧ v.HasPeriod p := by
  rw [isOverlap_iff_hasPeriod]
  constructor
  · rintro ⟨p, hp, hlen, per⟩
    exact ⟨p, mem_range.mpr (by omega), hp, hlen, per⟩
  · rintro ⟨p, _, hp, hlen, per⟩
    exact ⟨p, hp, hlen, per⟩

instance [DecidableEq α] (v : List α) : Decidable (IsOverlap v) :=
  decidable_of_iff _ isOverlap_iff_bounded.symm

end List
