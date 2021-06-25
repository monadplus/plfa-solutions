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
