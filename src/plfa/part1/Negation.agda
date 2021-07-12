module plfa.part1.Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_)
open import plfa.part1.Isomorphism using (_≃_; extensionality)

-----------------------------------------
-- Negation

-- Given a proposition A, the negation ¬ A holds if A cannot hold.
-- We formalise this idea by declaring negation to be the same as implication of false:

¬_ : Set → Set
¬ A = A → ⊥
infix 3 ¬_ -- ¬ A × ¬ B parses as (¬ A) × (¬ B) and ¬ m ≡ n as ¬ (m ≡ n).

-- This is a form of *reductio ad absurdum*:
-- if assuming A leads to the conclusion ⊥ (an absurdity), then we must have ¬ A.

-- Given evidence that both ¬ A and A hold, we can conclude that ⊥ holds.
-- In other words, if both ¬ A and A hold, then we have a contradiction:

¬-elim : ∀ {A : Set}
  → ¬ A
  → A
    ---
  → ⊥
¬-elim ¬x x = ¬x x
-- Note that this rule is just a special case of →-elim.

-- In classical logic, we have that A is equivalent to ¬ ¬ A.

-- As we discuss below, in Agda we use intuitionistic logic,
-- where we have only half of this equivalence, namely that A implies ¬ ¬ A:
¬¬-intro : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A
¬¬-intro x  =  λ{¬x → ¬x x}

-- An equivalent way to write the above is as follows:

¬¬-intro′ : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A
¬¬-intro′ x ¬x = ¬x x
