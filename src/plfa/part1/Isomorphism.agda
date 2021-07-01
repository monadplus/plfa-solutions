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
--
--   if two functions applied to the same argument always yield the same result, then they are the same function.
--
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
--
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

-- Isomorphism is an equivalence, meaning that it is reflexive, symmetric, and transitive.
--
-- To show isomorphism is reflexive, we take both to and from to be the identity function:

≃-refl : ∀ {A : Set}
     -----
  → A ≃ A
≃-refl =
  record
    { to      = λ{x → x}
    ; from    = λ{y → y}
    ; from∘to = λ{x → refl}
    ; to∘from = λ{y → refl}
    }

-- To show isomorphism is symmetric, we simply swap the roles of to and from, and from∘to and to∘from:

≃-sym : ∀ {A B : Set}
  → A ≃ B
     -----
  → B ≃ A
≃-sym A≃B =
  record
    { to      = from A≃B
    ; from    = to   A≃B
    ; from∘to = to∘from A≃B
    ; to∘from = from∘to A≃B
    }

-- To show isomorphism is transitive, we compose the to and from functions,
-- and use equational reasoning to combine the inverses:

≃-trans : ∀ {A B C : Set}
  → A ≃ B
  → B ≃ C
    -----
  → A ≃ C
≃-trans A≃B B≃C =
  record
    { to       = to   B≃C ∘ to   A≃B
    ; from     = from A≃B ∘ from B≃C
    ; from∘to  = λ{x →
        begin
          (from A≃B ∘ from B≃C) ((to B≃C ∘ to A≃B) x)
        ≡⟨⟩
          from A≃B (from B≃C (to B≃C (to A≃B x)))
        ≡⟨ cong (from A≃B) (from∘to B≃C (to A≃B x)) ⟩
          from A≃B (to A≃B x)
        ≡⟨ from∘to A≃B x ⟩
          x
        ∎}
    ; to∘from = λ{y →
        begin
          (to B≃C ∘ to A≃B) ((from A≃B ∘ from B≃C) y)
        ≡⟨⟩
          to B≃C (to A≃B (from A≃B (from B≃C y)))
        ≡⟨ cong (to B≃C) (to∘from A≃B (from B≃C y)) ⟩
          to B≃C (from B≃C y)
        ≡⟨ to∘from B≃C y ⟩
          y
        ∎}
     }

---------------------------------------------------------------------
-- Equational reasoning for isomorphism

-- It is straightforward to support a variant of equational reasoning for isomorphism.
-- We essentially copy the previous definition of equality for isomorphism.
-- We omit the form that corresponds to _≡⟨⟩_, since trivial isomorphisms arise far less often than trivial equalities:

module ≃-Reasoning where

  infix  1 ≃-begin_
  infixr 2 _≃⟨_⟩_
  infix  3 _≃-∎

  ≃-begin_ : ∀ {A B : Set}
    → A ≃ B
      -----
    → A ≃ B
  ≃-begin A≃B = A≃B

  _≃⟨_⟩_ : ∀ (A : Set) {B C : Set}
    → A ≃ B
    → B ≃ C
      -----
    → A ≃ C
  A ≃⟨ A≃B ⟩ B≃C = ≃-trans A≃B B≃C

  _≃-∎ : ∀ (A : Set)
      -----
    → A ≃ A
  A ≃-∎ = ≃-refl

open ≃-Reasoning

---------------------------------------------------------------------
-- Embedding

-- We also need the notion of *embedding,* which is a weakening of isomorphism.
-- While an isomorphism shows that two types are in one-to-one correspondence,
-- an embedding shows that the first type is included in the second; or, equivalently,
-- that there is a many-to-one correspondence between the second type and the first.

-- Here is the formal definition of embedding:

infix 0 _≲_
record _≲_ (A B : Set) : Set where
  field
    to      : A → B
    from    : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
open _≲_

-- Hence, we know that from is left-inverse to to, but not that from is right-inverse to to.

-- Embedding is reflexive and transitive, but not symmetric.

≲-refl : ∀ {A : Set} → A ≲ A
≲-refl =
  record
    { to      = λ{x → x}
    ; from    = λ{y → y}
    ; from∘to = λ{x → refl}
    }

≲-trans : ∀ {A B C : Set} → A ≲ B → B ≲ C → A ≲ C
≲-trans A≲B B≲C =
  record
    { to      = λ{x → to   B≲C (to   A≲B x)}
    ; from    = λ{y → from A≲B (from B≲C y)}
    ; from∘to = λ{x →
        begin
          from A≲B (from B≲C (to B≲C (to A≲B x)))
        ≡⟨ cong (from A≲B) (from∘to B≲C (to A≲B x)) ⟩
          from A≲B (to A≲B x)
        ≡⟨ from∘to A≲B x ⟩
          x
        ∎}
     }

-- It is also easy to see that if two types embed in each other,
-- and the embedding functions correspond, then they are isomorphic.
--
-- This is a weak form of anti-symmetry:

≲-antisym : ∀ {A B : Set}
  → (A≲B : A ≲ B)
  → (B≲A : B ≲ A)
  → (to A≲B ≡ from B≲A)
  → (from A≲B ≡ to B≲A)
     -------------------
  → A ≃ B
≲-antisym A≲B B≲A to≡from from≡to =
  record
    { to      = to A≲B
    ; from    = from A≲B
    ; from∘to = from∘to A≲B
    ; to∘from = λ{y →
        begin
          to A≲B (from A≲B y)
        ≡⟨ cong (to A≲B) (cong-app from≡to y) ⟩
          to A≲B (to B≲A y)
        ≡⟨ cong-app to≡from (to B≲A y) ⟩
          from B≲A (to B≲A y)
        ≡⟨ from∘to B≲A y ⟩
          y
        ∎}
    }

---------------------------------------------------------------------
-- Equational reasoning for embedding

module ≲-Reasoning where

  infix  1 ≲-begin_
  infixr 2 _≲⟨_⟩_
  infix  3 _≲-∎

  ≲-begin_ : ∀ {A B : Set}
    → A ≲ B
      -----
    → A ≲ B
  ≲-begin A≲B = A≲B

  _≲⟨_⟩_ : ∀ (A : Set) {B C : Set}
    → A ≲ B
    → B ≲ C
      -----
    → A ≲ C
  A ≲⟨ A≲B ⟩ B≲C = ≲-trans A≲B B≲C

  _≲-∎ : ∀ (A : Set)
      -----
    → A ≲ A
  A ≲-∎ = ≲-refl

open ≲-Reasoning

---------------------------------------------------------------------
-- Exercises

≃-implies-≲ : ∀ {A B : Set}
  → A ≃ B
    -----
  → A ≲ B
≃-implies-≲ A≃B =
  record
    { to      = to A≃B
    ; from    = from A≃B
    ; from∘to = from∘to A≃B
    }

-- Equivalence of preprositions (also known as "if and only if"):

infix 0 _⇔_
record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
open _⇔_

-- Show that equivalence is reflexive, symmetric, and transitive.

⇔-refl : ∀ {A : Set}
     ------
  → A ⇔ A
⇔-refl =
  record
    { to   = λ{x → x}
    ; from = λ{x → x}
    }

⇔-sym : ∀ {A B : Set}
  → A ⇔ B
     ------
  → B ⇔ A
⇔-sym A⇔B =
  record
    { to   = from A⇔B
    ; from = to A⇔B
    }

⇔-trans : ∀ {A B C : Set}
  → A ⇔ B
  → B ⇔ C
     ------
  → A ⇔ C
⇔-trans A⇔B B⇔C =
  record
    { to   = to B⇔C ∘ to A⇔B
    ; from = from A⇔B ∘ from B⇔C
    }

{-
Recall that Exercises Bin and Bin-laws define a datatype Bin of bitstrings representing natural numbers,
and asks you to define the following functions and predicates:

to : ℕ → Bin
from : Bin → ℕ

which satisfy the following property:

from (to n) ≡ n

Using the above, establish that there is an embedding of ℕ into Bin.
-}

open import plfa.part1.Induction using (Bin; ⟨⟩; _O; _I; inc; to; from; from∘to)

ℕ≲Bin : ℕ ≲ Bin
ℕ≲Bin = record
  { to      = plfa.part1.Induction.to
  ; from    = plfa.part1.Induction.from
  ; from∘to = plfa.part1.Induction.from∘to
  }

-- Why do to and from not form an isomorphism?

-- Only canonical bitstrings are isomorphic to natural numbers:
--
-- ℕ≲Can : ∀ (b : Bin)
--   → ℕ ≲ Can b

---------------------------------------------------------------------
-- Standard library

-- The standard library _↔_ and _↞_ correspond to our _≃_ and _≲_, respectively,
-- but those in the standard library are less convenient, since they depend on a nested record structure
-- and are parameterised with regard to an arbitrary notion of equivalence.

import Function using (_∘_)
import Function.Inverse using (_↔_)
import Function.LeftInverse using (_↞_)
