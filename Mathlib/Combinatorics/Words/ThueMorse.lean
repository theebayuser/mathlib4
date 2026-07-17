/-
Copyright (c) 2026 Daniel Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Liao
-/
module

public import Mathlib.Data.Nat.Digits.Lemmas

/-!
# The Thue–Morse sequence

`Nat.thueMorse n` is the parity of the number of `1`s in the binary expansion of `n`
(the Thue–Morse / Prouhet–Thue–Morse sequence, `true` = odd parity). It is defined here
as a `Bool`-valued sequence on `ℕ`; the classical `Fin 2` / `{0,1}`-word view is one
`if · then 1 else 0` away.

Main results are the defining recurrences that drive the overlap-free / cube-free proofs:

* `Nat.thueMorse_two_mul`: `thueMorse (2 * n) = thueMorse n`;
* `Nat.thueMorse_two_mul_add_one`: `thueMorse (2 * n + 1) = !thueMorse n`;
* `Nat.thueMorse_two_mul_ne`: consecutive even/odd values differ.

## References

* A. Thue, *Über unendliche Zeichenreihen*, 1906; *Über die gegenseitige Lage gleicher
  Teile gewisser Zeichenreihen*, 1912.
* [J.-P. Allouche, J. Shallit, *The ubiquitous Prouhet-Thue-Morse sequence*][allouche1999]

## Tags

Thue-Morse, Prouhet-Thue-Morse, combinatorics on words, overlap-free
-/

@[expose] public section

namespace Nat

/-- The Thue–Morse sequence: `thueMorse n` is `true` iff the binary expansion of `n` has an
odd number of `1`s. -/
def thueMorse (n : ℕ) : Bool := (Nat.digits 2 n).sum % 2 = 1

/-- The Thue–Morse sequence starts with `false` (zero has no binary `1`s). -/
@[simp] theorem thueMorse_zero : thueMorse 0 = false := rfl

/-- Unfolding lemma exposing the `decide` form of the definition, for rewriting the
coerced `Bool` without unfolding `thueMorse` itself. -/
theorem thueMorse_eq_decide (n : ℕ) :
    thueMorse n = decide ((Nat.digits 2 n).sum % 2 = 1) := rfl

/-- Even-index recurrence: `thueMorse (2 * n) = thueMorse n`. -/
theorem thueMorse_two_mul (n : ℕ) : thueMorse (2 * n) = thueMorse n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; rfl
  · have hpos : 0 < 2 * n := by omega
    unfold thueMorse
    rw [Nat.digits_def' (b := 2) (by norm_num) hpos]
    have h2 : (2 * n) % 2 = 0 := by omega
    have hd : (2 * n) / 2 = n := by omega
    rw [h2, hd, List.sum_cons, Nat.zero_add]

/-- Odd-index recurrence: `thueMorse (2 * n + 1) = !thueMorse n`. -/
theorem thueMorse_two_mul_add_one (n : ℕ) : thueMorse (2 * n + 1) = !thueMorse n := by
  have hpos : 0 < 2 * n + 1 := by omega
  unfold thueMorse
  rw [Nat.digits_def' (b := 2) (by norm_num) hpos]
  have h2 : (2 * n + 1) % 2 = 1 := by omega
  have hd : (2 * n + 1) / 2 = n := by omega
  rw [h2, hd, List.sum_cons]
  -- goal: `decide ((1 + s) % 2 = 1) = !decide (s % 2 = 1)`, split on parity of `s`
  rcases Nat.mod_two_eq_zero_or_one ((Nat.digits 2 n).sum) with h | h <;>
    simp [Nat.add_mod, h]

/-- Consecutive Thue–Morse values at an even/odd pair differ. -/
theorem thueMorse_two_mul_ne (n : ℕ) : thueMorse (2 * n) ≠ thueMorse (2 * n + 1) := by
  rw [thueMorse_two_mul, thueMorse_two_mul_add_one]
  cases thueMorse n <;> simp

end Nat
