module plfa.part1.Equality where

-- The definition features an asymmetry, in that the first argument to _≡_ is given by the parameter x : A,
-- while the second is given by an index in A → Set. This follows our policy of using parameters wherever possible.
--
-- The first argument to _≡_ can be a parameter because it doesn’t vary, while the second must be an index,
-- so it can be required to be equal to the first.

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_

--------------------------------------
-- Equality is an equivalence relation

-- Equivalence relation:
-- 1. reflexive
-- 2. symmetric
-- 3. transitive

-- The argument to sym has type x ≡ y, but on the left-hand side of the equation the
-- argument has been instantiated to the pattern refl, which requires that x and y are the same.
--
-- The book explains how to do this proof interactively.
sym : ∀ {A : Set} {x y : A}
  → x ≡ y
     -----
  → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
     -----
  → x ≡ z
trans refl refl = refl

-------------------------------
-- Congruence and substitution

cong : ∀ {A B : Set} (f : A → B) {x y : A}
  → x ≡ y
    ---------
  → f x ≡ f y
cong f refl  =  refl

cong₂ : ∀ {A B C : Set} (f : A → B → C) {u x : A} {v y : B}
  → u ≡ x
  → v ≡ y
    -------------
  → f u v ≡ f x y
cong₂ f refl refl  =  refl

cong-app : ∀ {A B : Set} {f g : A → B}
  → f ≡ g
    ---------------------
  → ∀ (x : A) → f x ≡ g x
cong-app refl x = refl

-- substitution:  If two values are equal and a predicate holds of the first then it also holds of the second.

subst : ∀ {A : Set} {x y : A} (P : A → Set)
  → x ≡ y
    ---------
  → P x → P y
subst P refl px = px

-------------------------------
-- Chains of equations

-- Nested Module

module ≡-Reasoning {A : Set} where

  infix  1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {x y : A}
    → x ≡ y
      -----
    → x ≡ y
  begin x≡y  =  x≡y

  _≡⟨⟩_ : ∀ (x : A) {y : A}
    → x ≡ y
      -----
    → x ≡ y
  x ≡⟨⟩ x≡y  =  x≡y

  _≡⟨_⟩_ : ∀ (x : A) {y z : A}
    → x ≡ y
    → y ≡ z
      -----
    → x ≡ z
  x ≡⟨ x≡y ⟩ y≡z  =  trans x≡y y≡z

  _∎ : ∀ (x : A)
      -----
    → x ≡ x
  x ∎  =  refl

-- Opening the module makes all of the definitions available in the current environment.
open ≡-Reasoning

trans′ : ∀ {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
    -----
  → x ≡ z
trans′ {A} {x} {y} {z} x≡y y≡z =
  begin
    x
  ≡⟨ x≡y ⟩
    y
  ≡⟨ y≡z ⟩
    z
  ∎
-- According to the fixity declarations, the body parses as follows:
--
-- begin (x ≡⟨ x≡y ⟩ (y ≡⟨ y≡z ⟩ (z ∎)))
--
-- The application of begin is purely cosmetic, as it simply returns its argument.
-- That argument consists of _≡⟨_⟩_ applied to x, x≡y, and y ≡⟨ y≡z ⟩ (z ∎).
--
-- After simplification, the body is equivalent to the term:
--
-- trans x≡y (trans y≡z refl)
--
-- We could replace any use of a chain of equations by a chain of applications of trans;
-- the result would be more compact but harder to read.

----------------------------------------------
-- Exercise trans and ≡-Reasoning (practice)

-- Sadly, we cannot use the definition of trans’ using ≡-Reasoning as the definition for trans.
-- Can you see why? (Hint: look at the definition of _≡⟨_⟩_)
--
-- Answer: we cannot define trans in terms of _≡⟨_⟩_ because _≡⟨_⟩_ is defined in terms of trans which would not terminate.

----------------------------------------------
-- Chains of equations, another example

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero    + n  =  n
(suc m) + n  =  suc (m + n)

-- Postulates must be used with caution.
-- If we postulate something false then we could use Agda to prove anything whatsoever.

postulate
  +-identity : ∀ (m : ℕ) → m + zero ≡ m
  +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identity m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎

-- Agda always treats a term as equivalent to its simplified term. The reason that one can write
--
-- suc (n + m)
-- ≡⟨⟩
-- suc n + m
--
-- is because Agda treats both terms as the same.

-----------------------------------------------------------
-- Exercise ≤-Reasoning (stretch)

data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ}
      --------
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}
    → m ≤ n
      -------------
    → suc m ≤ suc n
infix 4 _≤_

postulate
  ≤-refl : ∀ {n : ℕ}
       -----
    → n ≤ n

  ≤-trans : ∀ {m n p : ℕ}
    → m ≤ n
    → n ≤ p
      -----
    → m ≤ p

module ≤-Reasoning where

  infix  1 start_
  infixr 2 _≤⟨⟩_ _≤⟨_⟩_
  infix  3 _end

  start_ : ∀ {n m : ℕ}
    → n ≤ m
       -----
    → n ≤ m
  start x≤y  =  x≤y

  _≤⟨⟩_ : ∀ (m : ℕ) {n : ℕ}
    → m ≤ n
       -----
    → m ≤ n
  m ≤⟨⟩ m≤n  = m≤n

  _≤⟨_⟩_ : ∀ (m : ℕ) {n p : ℕ}
    → m ≤ n
    → n ≤ p
       -----
    → m ≤ p
  m ≤⟨ m≤n ⟩ n≤p  = ≤-trans m≤n n≤p

  _end : ∀ (n : ℕ)
       -----
    → n ≤ n
  n end  = ≤-refl

open ≤-Reasoning

+-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
     -------------
  → n + p ≤ n + q
+-monoʳ-≤ zero p q p≤q =
  start
    zero + p
  ≤⟨⟩
    p
  ≤⟨ p≤q ⟩
    q
  ≤⟨⟩
    zero + q
  end
+-monoʳ-≤ (suc n) p q p≤q =
  start
    suc n + p
  ≤⟨⟩
    suc (n + p)
  ≤⟨ s≤s (+-monoʳ-≤ n p q p≤q) ⟩
    suc (n + q)
  ≤⟨⟩
    suc n + q
  end

≡-implies-≤ : ∀ {m n : ℕ}
  → m ≡ n
     -----
  → m ≤ n
≡-implies-≤ {zero} refl = z≤n
≡-implies-≤ {suc m} {suc n} refl = s≤s (≡-implies-≤ refl)

+-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
     -------------
  → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n =
  start
    m + p
  ≤⟨ ≡-implies-≤ (+-comm m p)⟩
    p + m
  ≤⟨ +-monoʳ-≤  p m n m≤n ⟩
    p + n
  ≤⟨ ≡-implies-≤ (+-comm p n)⟩
    n + p
  end

+-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
     -------------
  → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q =
  start
    m + p
  ≤⟨ +-monoˡ-≤ m n p m≤n ⟩
    n + p
  ≤⟨ +-monoʳ-≤ n p q p≤q ⟩
    n + q
  end

------------------------------------------
-- Rewriting

data even : ℕ → Set
data odd  : ℕ → Set

data even where

  even-zero : even zero

  even-suc : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)

-- In the previous section, we proved addition is commutative.
-- Given evidence that even (m + n) holds, we ought also to be able to take that as evidence that even (n + m) holds.
--
-- Agda includes special notation to support just this kind of reasoning, the rewrite notation we encountered earlier.
-- To enable this notation, we use pragmas to tell Agda which type corresponds to equality:

{-# BUILTIN EQUALITY _≡_ #-}

even-comm : ∀ (m n : ℕ)
  → even (m + n)
    ------------
  → even (n + m)
even-comm m n ev rewrite +-comm n m  =  ev

-----------------------------------------------------
-- Multiple rewrites

-- rewriting automatically takes congruence into account.

+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ zero    n  rewrite +-identity n             = refl
+-comm′ (suc m) n  rewrite +-comm′ m n  | +-suc n m = refl

-- Although proofs with rewriting are shorter, proofs as chains of equalities are
-- easier to follow, and we will stick with the latter when feasible.

-----------------------------------------------------
-- Rewriting expanded

--  The rewrite notation is in fact shorthand for an appropriate use of with abstraction:

even-comm′ : ∀ (m n : ℕ)
  → even (m + n)
    ------------
  → even (n + m)
even-comm′ m n ev with   m + n  | +-comm m n
...                  | .(n + m) | refl       = ev

-- m + n is matched against .(n + m)
-- +-comm m n is matched against refl

-- Here the first column asserts that m + n and n + m are identical,
-- and the second column justifies that assertion with evidence of the appropriate equality.
--
-- Note also the use of the dot pattern, .(n + m)
-- A dot pattern consists of a dot followed by an expression, and
-- is used when other information forces the value matched to be equal
-- to the value of the expression in the dot pattern.
--
-- In this case, the identification of m + n and n + m is justified by the subsequent
-- matching of +-comm m n against refl.
--
-- One might think that the first clause is redundant as the information is inherent in the second clause,
-- but in fact Agda is rather picky on this point: omitting the first clause or
-- reversing the order of the clauses will cause Agda to report an error. (Try it and see!)

--  In this case, we can avoid rewrite by simply applying the substitution function defined earlier:

even-comm″ : ∀ (m n : ℕ)
  → even (m + n)
    ------------
  → even (n + m)
even-comm″ m n  =  subst even (+-comm m n)
-- subst : ∀ {A : Set} {x y : A} (P : A → Set)
--   → x ≡ y
--     ---------
--   → P x → P y
-- subst P refl px = px

----------------------------------------------------
-- Leibniz equality


-- The form of asserting equality that we have used is due to Martin Löf, and was published in 1975.
-- An older form is due to Leibniz, and was published in 1686.
--
-- Leibniz asserted the identity of indiscernibles:
--   two objects are equal if and only if they satisfy the same properties.

-- Here we define Leibniz equality, and show that
--   two terms satisfy Leibniz equality if and only if they satisfy Martin Löf equality.

-- Leibniz equality is usually formalised to state that
--   x ≐ y holds if every property P that holds of x also holds of y.
--
-- Perhaps surprisingly, this definition is sufficient to also ensure the converse,
-- that every property P that holds of y also holds of x.

-- Let x and y be objects of type A.
-- We say that x ≐ y holds if for every predicate P over type A we have that P x implies P y:

_≐_ : ∀ {A : Set} (x y : A) → Set₁
_≐_ {A} x y = ∀ (P : A → Set) → P x → P y

-- This is our first use of **levels**.
-- We cannot assign Set the type Set, since this would lead to contradictions such as Russell’s Paradox and Girard’s Paradox.
--
-- Instead, there is a hierarchy of types, where Set : Set₁, Set₁ : Set₂, and so on.
--
-- In fact, Set itself is just an abbreviation for Set₀.
--
-- Since the equation defining _≐_ mentions Set on the right-hand side,
-- the corresponding signature must use Set₁. We say a bit more about levels below.

-- Leibniz equality is reflexive and transitive,
-- where the first follows by a variant of the identity function
-- and the second by a variant of function composition:

refl-≐ : ∀ {A : Set} {x : A}
  → x ≐ x
refl-≐ P Px  =  Px

trans-≐ : ∀ {A : Set} {x y z : A}
  → x ≐ y
  → y ≐ z
    -----
  → x ≐ z
trans-≐ x≐y y≐z P Px  =  y≐z P (x≐y P Px)

-- We have to show that if P x implies P y for all predicates P, then the implication holds the other way round as well:

-- Given x ≐ y, a specific P, we have to construct a proof that P y implies P x.
-- To do so, we instantiate the equality with a predicate Q such that Q z holds
-- if P z implies P x. The property Q x is trivial by reflexivity, and
-- hence Q y follows from x ≐ y. But Q y is exactly a proof of what we require,
-- that P y implies P x.

sym-≐ : ∀ {A : Set} {x y : A}
  → x ≐ y
     -----
  → y ≐ x
sym-≐ {A} {x} {y} x≐y P  =  Qy
  where
    Q : A -> Set
    Q z = P z -> P x
    Qx : Q x
    Qx = refl-≐ P
    Qy : Q y
    Qy = x≐y Q Qx

--  We now show that Martin Löf equality implies Leibniz equality, and vice versa.
--  In the forward direction, if we know x ≡ y we need for any P to take evidence of P x to evidence of P y,
--  which is easy since equality of x and y implies that any proof of P x is also a proof of P y:

≡-implies-≐ : ∀ {A : Set} {x y : A}
  → x ≡ y
     -----
  → x ≐ y
≡-implies-≐ x≡y P  =  subst P x≡y

-- In the reverse direction, given that for any P we can take a proof of P x to a proof of P y we need to show x ≡ y:
--
-- The proof is similar to that for symmetry of Leibniz equality.
-- We take Q to be the predicate that holds of z if x ≡ z. Then Q x is trivial by reflexivity of Martin Löf equality, and hence Q y follows from x ≐ y. But Q y is exactly a proof of what we require, that x ≡ y.

≐-implies-≡ : ∀ {A : Set} {x y : A}
  → x ≐ y
     -----
  → x ≡ y
≐-implies-≡ {A} {x} {y} x≐y  =  Qy
  where
    Q : A → Set
    Q z = x ≡ z
    Qx : Q x
    Qx = refl
    Qy : Q y
    Qy = x≐y Q Qx

-------------------------------------------------------------
-- Universe polymorphism

-- The definition of equality given above is fine if we want to compare two values of a type that belongs to Set,
-- but what if we want to compare two values of a type that belongs to Set ℓ for some arbitrary level ℓ?
--
-- The answer is **universe polymorphism**, where a definition is made with respect to an arbitrary level ℓ.
-- To make use of levels, we first import the following:

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)

-- We rename constructors zero and suc to lzero and lsuc to avoid confusion between levels and naturals.

-- Levels are isomorphic to natural numbers, and have similar constructors:

-- lzero : Level
-- lsuc  : Level → Level

-- _⊔_ : Level → Level → Level
-- Given two levels returns the larger of the two.

data _≡′_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl′ : x ≡′ x

-- For simplicity, we avoid universe polymorphism in the definitions given in the text,
-- but most definitions in the standard library, including those for equality,
-- are generalised to arbitrary levels as above.

--  Here is the generalised definition of Leibniz equality:


_≐′_ : ∀ {ℓ : Level} {A : Set ℓ} (x y : A) → Set (lsuc ℓ)
_≐′_ {ℓ} {A} x y = ∀ (P : A → Set ℓ) → P x -> P y

-- Most other functions in the standard library are also generalised to arbitrary levels.
-- For instance, here is the definition of composition.

_∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
  → (B → C) → (A → B) → A → C
(g ∘ f) x  =  g (f x)

-- More info at https://agda.readthedocs.io/en/v2.6.1/language/universe-levels.html

----------------------------------------------------------------------------------
-- Standard library

-- Definitions similar to those in this chapter can be found in the standard library.
-- The Agda standard library defines _≡⟨_⟩_ as step-≡, which reverses the order of the arguments.
--
-- The standard library also defines a syntax macro, which is automatically imported whenever you import step-≡,
-- which recovers the original argument order:

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
