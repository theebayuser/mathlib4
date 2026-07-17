/-
Copyright (c) 2026 Daniel Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Liao
-/
module

public import Mathlib.Algebra.FreeMonoid.Basic

/-!
# Uniform substitutions on words

A *substitution* (a morphism of free monoids that need not rename letters one-for-one) is
modelled on lists by `List.flatMap h` for a map `h : α → List β`. This file adds the small
generic API a combinatorics-on-words development needs:

* `List.IsUniform h ℓ`: every letter image `h a` has the same length `ℓ`;
* `List.length_flatMap_of_uniform`: a uniform substitution multiplies length by `ℓ`;
* `FreeMonoid.toList_lift_ofList`: the bridge identifying the free-monoid homomorphism
  `FreeMonoid.lift (fun a => FreeMonoid.ofList (h a))` with the computational
  `List.flatMap h`. This is what lets a substitution be treated as a bundled
  `FreeMonoid α →* FreeMonoid β` while still computing on lists.

## Tags

combinatorics on words, substitution, morphism, uniform morphism, free monoid
-/

@[expose] public section

namespace List

variable {α β : Type*}

/-- A substitution `h : α → List β` is `ℓ`-*uniform* if every letter image has
length `ℓ`. -/
def IsUniform (h : α → List β) (ℓ : ℕ) : Prop := ∀ a, (h a).length = ℓ

/-- A uniform substitution multiplies word length by the uniform image length:
`|w.flatMap h| = ℓ * |w|`. -/
theorem length_flatMap_of_uniform {h : α → List β} {ℓ : ℕ} (hh : IsUniform h ℓ)
    (w : List α) : (w.flatMap h).length = ℓ * w.length := by
  induction w with
  | nil => simp
  | cons a w ih =>
      rw [List.flatMap_cons, List.length_append, hh a, ih, List.length_cons,
        Nat.mul_succ]
      omega

end List

namespace FreeMonoid

variable {α β : Type*}

/-- **Substitution bridge.** The free-monoid homomorphism induced by a substitution
`h : α → List β` (sending each letter `a` to the word `h a`) computes, on the underlying
lists, as `List.flatMap h`. Concretely, `lift (ofList ∘ h)` applied to `ofList w` has
underlying list `w.flatMap h`.

This identifies the bundled `FreeMonoid α →* FreeMonoid β` view of a substitution with the
concrete list operation, so proofs may use whichever is convenient. -/
theorem toList_lift_ofList (h : α → List β) (w : List α) :
    (FreeMonoid.lift (fun a => FreeMonoid.ofList (h a)) (FreeMonoid.ofList w)).toList
      = w.flatMap h := by
  induction w with
  | nil => simp
  | cons a w ih =>
      have hcons : FreeMonoid.ofList (a :: w)
          = FreeMonoid.of a * FreeMonoid.ofList w := rfl
      rw [hcons, map_mul, FreeMonoid.toList_mul, ih, FreeMonoid.lift_eval_of,
        List.flatMap_cons]
      rfl

end FreeMonoid
