module plfa.part1.Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _∸_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_ ; _,_)
open import plfa.part1.Isomorphism using (_≃_; extensionality)
open import plfa.part1.Relations using (_<_)

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
--
-- As we discuss below, in Agda we use *intuitionistic logic*,
-- where we have only half of this equivalence, namely that A implies ¬ ¬ A:

¬¬-intro : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A
¬¬-intro x  =  λ{¬x → ¬x x}
-- We show that assuming ¬ A leads to a contradiction, and hence ¬ ¬ A must hold

-- An equivalent way to write the above is as follows:

¬¬-intro′ : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A
¬¬-intro′ x ¬x = ¬x x

--  We cannot show that ¬ ¬ A implies A, but we can show that ¬ ¬ ¬ A implies ¬ A:

¬¬¬-elim : ∀ {A : Set}
  → ¬ ¬ ¬ A
    -------
  → ¬ A
¬¬¬-elim ¬¬¬x  =  λ x → ¬¬¬x (¬¬-intro x)

--  Another law of logic is *contraposition,* stating that if A implies B, then ¬ B implies ¬ A:

contraposition : ∀ {A B : Set}
  → (A → B)
    -----------
  → (¬ B → ¬ A)
contraposition f ¬y x = ¬y (f x)

-- Using negation, it is straightforward to define inequality:

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y  =  ¬ (x ≡ y)

-- It is trivial to show distinct numbers are not equal:
_ : 1 ≢ 2
_ = λ()

-- This is our first use of an absurd pattern in a lambda expression.
-- The type M ≡ N is occupied exactly when M and N simplify to identical terms.
-- Since 1 and 2 simplify to distinct normal forms, Agda determines that there is
-- no possible evidence that 1 ≡ 2.
--
-- As a second example, it is also easy to validate Peano’s postulate that zero
-- is not the successor of any number:

peano : ∀ {m : ℕ} → zero ≢ suc m
peano = λ()

-- Given the correspondence of implication to exponentiation
-- and false to the type with no members,
-- we can view *negation as raising to the zero power*.

-- This indeed corresponds to what we know for arithmetic, where

-- 0 ^ n  ≡  1,  if n ≡ 0
--        ≡  0,  if n ≢ 0
--
-- Indeed, there is exactly one proof of ⊥ → ⊥. We can write this proof two different ways:

id : ⊥ → ⊥
id x = x

id′ : ⊥ → ⊥
id′ ()

-- But, using extensionality, we can prove these equal:

id≡id′ : id ≡ id′
id≡id′ = extensionality (λ())

-- Indeed, we can show any two proofs of a negation are equal:

assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation ¬x ¬x′ = extensionality (λ x → ⊥-elim (¬x x))


--------------------------------------------------------
-- Exercises

open _<_

<-irreflexive : ∀ {n : ℕ} → ¬ (n < n)
<-irreflexive (s<s n) = <-irreflexive n
-- if z<s n then n ≡ zero and n ≡ suc zero which is an absurd case.
-- We only need to recurse until we find that case

data Trichotomy (m n : ℕ) : Set where

  less :
          (m < n)
      → ¬ (m ≡ n)
      → ¬ (n < m)
      -----
    → Trichotomy m n

  equal :
        ¬ (m < n)
      →   (m ≡ n)
      → ¬ (n < m)
      -----
    → Trichotomy m n

  greater :
        ¬ (m < n)
      → ¬ (m ≡ n)
      → (n < m)
      -----
    → Trichotomy m n

trichotomy : ∀ (m n : ℕ) → Trichotomy m n
trichotomy zero zero = equal (λ()) refl (λ())
trichotomy zero (suc n) = less z<s (λ()) (λ())
trichotomy (suc m) zero = greater (λ()) (λ()) z<s
trichotomy (suc m) (suc n) with trichotomy m n
... | less     m<n ¬m≡n  ¬n<m = less (s<s m<n) (λ{sucₘ≡sucₙ → ¬m≡n (cong (λ x → x ∸ 1) sucₘ≡sucₙ)}) (λ{(s<s n<m) → ¬n<m n<m})
... | equal   ¬m<n  m≡n  ¬n<m = equal (λ{(s<s m<n) → ¬m<n m<n}) (cong suc m≡n) (λ{(s<s n<m) → ¬n<m n<m})
... | greater ¬m<n ¬m≡n   n<m = greater (λ{(s<s m<n) → ¬m<n m<n}) (λ{sucₘ≡sucₙ → ¬m≡n (cong (λ x → x ∸ 1) sucₘ≡sucₙ)}) (s<s n<m)

-- Show that conjunction, disjunction, and negation are related by a version of De Morgan’s Law.
--   ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)

postulate
  →-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))

⊎-dual-× : ∀ {A B : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
⊎-dual-× = →-distrib-⊎

-- Do we also have the following?
--   ¬ (A × B) ≃ (¬ A) ⊎ (¬ B)
-- If so, prove; if not, can you give a relation weaker than isomorphism that relates the two sides?

open import plfa.part1.Isomorphism using (_≲_ ; _⇔_)

open _≲_
open _⇔_

-- ×-dual-⊎ : ¬ (A × B) ≲ (¬ A) ⊎ (¬ B)
-- ×-dual-⊎ : ∀ {A B : Set} → ¬ (A × B) ⇔ (¬ A) ⊎ (¬ B)

×-dual-⊎ : ∀ {A B : Set} → (¬ A) ⊎ (¬ B) → ¬ (A × B)
×-dual-⊎ (inj₁ ¬A) (A , _) = ¬A A
×-dual-⊎ (inj₂ ¬B) (_ , B) = ¬B B

--------------------------------------------------
-- Intuitive and Classical logic
