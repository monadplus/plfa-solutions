module plfa.part1.Isomorphism where

-- This section introduces *isomorphism* as a way of asserting that two types are equal,
-- and *embedding* as a way of asserting that one type is smaller than another.
--
-- We apply isomorphisms in the next chapter to demonstrate that operations on types
-- such as product and sum satisfy properties akin to associativity, commutativity, and distributivity.

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)

---------------------------------------------------------------------
-- Lambda expressions

{-
Lambda expressions provide a compact way to define functions without naming them. A term of the form

 λ{ P₁ → N₁; ⋯ ; Pₙ → Nₙ }

is equivalent to a function f defined by the equations

 f P₁ = N₁
 ⋯
 f Pₙ = Nₙ

where the Pₙ are patterns (left-hand sides of an equation) and the Nₙ are expressions (right-hand side of an equation).

In the case that there is one equation and the pattern is a variable, we may also use the syntax

 λ x → N

 or

 λ (x : A) → N

both of which are equivalent to λ{x → N}.
-}

---------------------------------------------------------------------
-- Function composition

_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
(g ∘ f) x  = g (f x)

-- An equivalent definition, exploiting lambda expressions, is as follows:

_∘′_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
g ∘′ f  =  λ x → g (f x)


---------------------------------------------------------------------
-- Extensionality

-- *Extensionality* asserts that the only way to distinguish functions is by applying them;
-- if two functions applied to the same argument always yield the same result, then they are the same function.
-- It is the converse of cong-app, as introduced earlier.

--  Agda does not presume extensionality, but we can postulate that it holds:

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

-- Postulating extensionality does not lead to difficulties, as it is known to be consistent with the theory that underlies Agda.

-- As an example, consider that we need results from two libraries, one where
-- addition is defined, as in Chapter Naturals, and one where it is defined the other way around.

_+′_ : ℕ → ℕ → ℕ
m +′ zero  = m
m +′ suc n = suc (m +′ n)

-- Applying commutativity, it is easy to show that both operators always return the same result given the same arguments:

same-app : ∀ (m n : ℕ) → m +′ n ≡ m + n
same-app m n rewrite +-comm m n = helper m n
  where
  helper : ∀ (m n : ℕ) → m +′ n ≡ n + m
  helper m zero    = refl
  helper m (suc n) = cong suc (helper m n)

-- However, it might be convenient to assert that the two operators are actually indistinguishable.
-- This we can do via two applications of extensionality:

same : _+′_ ≡ _+_
same = extensionality (λ m → extensionality (λ n → same-app m n))

-- More generally, we may wish to postulate extensionality for dependent functions.

postulate
  ∀-extensionality : ∀ {A : Set} {B : A → Set} {f g : ∀(x : A) → B x}
    → (∀ (x : A) → f x ≡ g x)
       ------------------------
    → f ≡ g

-- Here the type of f and g has changed from A → B to ∀ (x : A) → B x,
-- generalising ordinary functions to dependent functions.

---------------------------------------------------------------------
-- Isomorphism

-- Two sets are isomorphic if they are in one-to-one correspondence.
--
-- Here is a formal definition of isomorphism:

infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≃_

{-
An isomorphism between sets A and B consists of four things:

- A function to from A to B,
- A function from from B back to A
- Evidence from∘to asserting that from is a left-inverse for to
- Evidence to∘from asserting that from is a right-inverse for to.

In particular, the third asserts that from ∘ to is the identity,
and the fourth that to ∘ from is the identity, hence the names.

The declaration open _≃_ makes available the names to, from, from∘to, and to∘from,
otherwise we would need to write _≃_.to and so on.
-}

-- The above is our first use of records.
-- A record declaration behaves similar to a single-constructor data declaration
-- (there are minor differences, which we discuss in Connectives):

data _≃′_ (A B : Set): Set where
  mk-≃′ : ∀ (to : A → B) →
          ∀ (from : B → A) →
          ∀ (from∘to : (∀ (x : A) → from (to x) ≡ x)) →
          ∀ (to∘from : (∀ (y : B) → to (from y) ≡ y)) →
          A ≃′ B

to′ : ∀ {A B : Set} → (A ≃′ B) → (A → B)
to′ (mk-≃′ f g g∘f f∘g) = f

from′ : ∀ {A B : Set} → (A ≃′ B) → (B → A)
from′ (mk-≃′ f g g∘f f∘g) = g

from∘to′ : ∀ {A B : Set} → (A≃B : A ≃′ B) → (∀ (x : A) → from′ A≃B (to′ A≃B x) ≡ x)
from∘to′ (mk-≃′ f g g∘f f∘g) = g∘f

to∘from′ : ∀ {A B : Set} → (A≃B : A ≃′ B) → (∀ (y : B) → to′ A≃B (from′ A≃B y) ≡ y)
to∘from′ (mk-≃′ f g g∘f f∘g) = f∘g

{-
We construct values of the record type with the syntax

record
  { to    = f
  ; from  = g
  ; from∘to = g∘f
  ; to∘from = f∘g
  }

which corresponds to using the constructor of the corresponding inductive type

mk-≃′ f g g∘f f∘g

where f, g, g∘f, and f∘g are values of suitable types.
-}

---------------------------------------------------------------------
-- Isomorphism is an equivalence

---------------------------------------------------------------------
-- Equational reasoning for isomorphism

---------------------------------------------------------------------
-- Embedding

---------------------------------------------------------------------
-- Equational reasoning for embedding

---------------------------------------------------------------------
-- Standard library
