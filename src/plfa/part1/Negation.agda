module plfa.part1.Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _∸_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
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

{-

Logic comes in many varieties, and one distinction is between *classical* and *intuitionistic*.

Intuitionists, concerned by assumptions made by some logicians about the nature of infinity,
insist upon a constructionist notion of truth.

In particular, they insist that a proof of A ⊎ B must show which of A or B holds

Intuitionists also reject the law of the excluded middle,
which asserts A ⊎ ¬ A for every A, since the law gives no clue as to which of A or ¬ A holds.

Heyting formalised a variant of Hilbert’s classical logic that captures the intuitionistic notion of provability.
In particular, the law of the excluded middle is provable in Hilbert’s logic, but not in Heyting’s.

Further, if the law of the excluded middle is added as an axiom to Heyting’s logic,
then it becomes equivalent to Hilbert’s.

Kolmogorov showed the two logics were closely related: he gave a double-negation translation, such that
a formula is provable in classical logic if and only if its translation is provable in intuitionistic logic.

Propositions as Types was first formulated for intuitionistic logic.
It is a perfect fit, because in the intuitionist interpretation the
formula A ⊎ B is provable exactly when one exhibits either a proof of A or a proof of B,
so the type corresponding to disjunction is a disjoint sum.

(Parts of the above are adopted from “Propositions as Types”, Philip Wadler, Communications of the ACM, December 2015.)
-}

-------------------------------------------------
-- Exlucded middle is irrefutable

--  The law of the excluded middle can be formulated as follows:

postulate
  em : ∀ {A : Set} → A ⊎ ¬ A

-- As we noted, the law of the excluded middle does not hold in intuitionistic logic.
--
-- However, we can show that it is irrefutable, meaning that the negation of its negation is provable
-- (and hence that its negation is never provable):

em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable k = k (inj₂ λ{ x → k (inj₁ x) })

---------------------------------------------
-- Exercise Classical (stretch)

{-
Consider the following principles:

    Excluded Middle: A ⊎ ¬ A, for all A
    Double Negation Elimination: ¬ ¬ A → A, for all A
    Peirce’s Law: ((A → B) → A) → A, for all A and B.
    Implication as disjunction: (A → B) → ¬ A ⊎ B, for all A and B.
    De Morgan: ¬ (¬ A × ¬ B) → A ⊎ B, for all A and B.

Show that each of these implies all the others.
-}

em→¬¬ : ∀ {A : Set}
  → (A ⊎ ¬ A)
     ------------
  → (¬ ¬ A → A)
em→¬¬ (inj₁ A) _ = A
em→¬¬ (inj₂ ¬A) ¬¬A = ⊥-elim (¬¬A ¬A)

em→Peirce : ∀ {A B : Set}
  → (A ⊎ ¬ A)
     ----------------------
  → (((A → B) → A) → A)
em→Peirce (inj₁ A) f = A
em→Peirce (inj₂ ¬A) f = f (λ A → ⊥-elim (¬A A))

em→→⊎ : ∀ {A B : Set}
  → (A ⊎ ¬ A)
     ---------------------
  → ((A → B) → ¬ A ⊎ B)
em→→⊎ (inj₁ A) f = inj₂ (f A)
em→→⊎ (inj₂ ¬A) _ = inj₁ ¬A

-- em→deMorgan :
--   (∀ {A : Set} → (A ⊎ ¬ A))
--   -------------------------------------------------
--   → (∀ {A' B : Set} → (¬ (¬ A' × ¬ B) → A' ⊎ B))
-- em→deMorgan f {A'} {B} with f {A'}
-- ... | (inj₁ A) = λ _ → inj₁ A
-- ... | (inj₂ ¬A) = λ neg-¬A×¬B → inj₂ (⊥-elim (neg-¬A×¬B (¬A , ¬A)))

¬¬→deMorgan :
     (∀ {A : Set} → (¬ ¬ A → A))
     ------------------------
  → (∀ {A' B : Set} → ¬ (¬ A' × ¬ B) → A' ⊎ B)
¬¬→deMorgan ¬¬A→A ¬⟨¬A,¬B⟩ =
  ¬¬A→A (λ ¬-A⊎B → ¬⟨¬A,¬B⟩ ((λ A → ¬-A⊎B (inj₁ A)) , λ B → ¬-A⊎B (inj₂ B)))
-- the key here is to instantiate the A=A⊎B in ¬¬A→A.

Stable : Set → Set
Stable A = ¬ ¬ A → A

-- Show that any negated formula is stable:
neg-stable : ∀ {A : Set}
     ------------
  → Stable (¬ A)
neg-stable ¬¬¬A = ¬¬¬-elim ¬¬¬A

-- Show that the conjunction of two stable formulas is stable:
×-stable : ∀ {A B : Set}
  → Stable A
  → Stable B
  → Stable (A × B)
×-stable stableA stableB ¬-A×B =
  ( stableA (λ ¬A → ¬-A×B (λ A×B → ¬A (proj₁ A×B))) , stableB (λ ¬B → ¬-A×B (λ A×B → ¬B (proj₂ A×B))))

--------------------------------------------------------
-- Standard Prelude

import Relation.Nullary using (¬_)
import Relation.Nullary.Negation using (contraposition)
