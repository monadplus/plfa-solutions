module plfa.part1.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)

-- Union and Intersection are associative, commutative
--   and intersection distributes over union.
--
-- Difference is associative but not commutative.
-- It also distributes over union and intersection.

-----------------------------------
-- Associativity

_ : (3 + 4) + 5 ≡ 3 + (4 + 5)
_ =
  begin
    (3 + 4) + 5
  ≡⟨⟩
    7 + 5
  ≡⟨⟩
    12
  ≡⟨⟩
    3 + 9
  ≡⟨⟩
    3 + (4 + 5)
  ∎

-- Proof by induction (for all natural numbers)

{-
------
P zero

P m
---------
P (suc m)
-}


+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

-- Induction as recursion

+-assoc-2 : ∀ (n p : ℕ) → (2 + n) + p ≡ 2 + (n + p)
+-assoc-2 n p =
  begin
    (2 + n) + p
  ≡⟨⟩
    suc (1 + n) + p
  ≡⟨⟩
    suc ((1 + n) + p)
  ≡⟨ cong suc (+-assoc-1 n p) ⟩
    suc (1 + (n + p))
  ≡⟨⟩
    2 + (n + p)
  ∎
  where
  +-assoc-1 : ∀ (n p : ℕ) → (1 + n) + p ≡ 1 + (n + p)
  +-assoc-1 n p =
    begin
      (1 + n) + p
    ≡⟨⟩
      suc (0 + n) + p
    ≡⟨⟩
      suc ((0 + n) + p)
    ≡⟨ cong suc (+-assoc-0 n p) ⟩
      suc (0 + (n + p))
    ≡⟨⟩
      1 + (n + p)
    ∎
    where
    +-assoc-0 : ∀ (n p : ℕ) → (0 + n) + p ≡ 0 + (n + p)
    +-assoc-0 n p =
      begin
        (0 + n) + p
      ≡⟨⟩
        n + p
      ≡⟨⟩
        0 + (n + p)
      ∎

-- +-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
-- +-assoc : ∀ (m : ℕ) → ∀ (n : ℕ) → ∀ (p : ℕ) → (m + n) + p ≡ m + (n + p)

-----------------------------------
-- Commutativity

-- We need two lemmas to proof commutativity of natural numbers

-- +-identityʳ is given by addition base case
--
-- Lemma 1
+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎
+-identityʳ (suc m) =
  begin
    suc m + zero
  ≡⟨⟩
    suc (m + zero)
  ≡⟨ cong suc (+-identityʳ m) ⟩
    suc m
  ∎

-- Inductive case in addition: suc m + n ≡ suc (m + n)
--
-- Lemma 2: m + succ n ≡ suc (m + n)
+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n =
  begin
    zero + suc n
  ≡⟨⟩
    suc n
  ≡⟨⟩
    suc (zero + n)
  ∎
+-suc (suc m) n =
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n))
  ≡⟨⟩
    suc (suc m + n)
  ∎


+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identityʳ m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + (suc n)
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎

-----------------------------------
-- Corollary: Rearranging

+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ +-assoc m n (p + q) ⟩
    m + (n + (p + q))
  ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩
    m + ((n + p) + q)
  ≡⟨ sym (+-assoc m (n + p) q) ⟩
    (m + (n + p)) + q
  ∎

-----------------------------------
-- Associativity with rewrite

+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ zero    n p                          =  refl
+-assoc′ (suc m) n p  rewrite +-assoc′ m n p  =  refl

-----------------------------------
-- Commutativity with rewrite

-- Order of rewrites matter.

+-identity′ : ∀ (n : ℕ) -> n + zero ≡ n
+-identity′ zero = refl
+-identity′ (suc n) rewrite +-identity′ n = refl

+-suc′ : ∀ (m n : ℕ) -> m + suc n ≡ suc (m + n)
+-suc′ zero n = refl
+-suc′ (suc m) n rewrite +-suc′ m n = refl

+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ m zero rewrite +-identity′ m = refl
+-comm′ m (suc n) rewrite +-suc′ m n | +-comm′ m n = refl

-----------------------------------
-- Exercises

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p rewrite sym (+-assoc′ m n p)
                   | +-comm′ m n
                   | +-assoc′ n m p = refl

-- _*_ : Nat → Nat → Nat
-- zero  * m = zero
-- suc n * m = m + n * m

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p rewrite *-distrib-+ m n p | sym (+-assoc′ p (m * p) (n * p)) = refl

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p rewrite *-distrib-+ n (m * n) p | *-assoc m n p = refl

*-zeroʳ : ∀ (n : ℕ) → n * zero ≡ zero
*-zeroʳ zero = refl
*-zeroʳ (suc n) rewrite *-zeroʳ n = refl

*-suc : ∀ (m n : ℕ) → m * suc n ≡ m + m * n
*-suc zero n = refl
*-suc (suc m) n rewrite
    *-suc m n
  | sym (+-assoc n m (m * n))
  | +-comm n m
  | +-assoc m n (m * n)
  = refl

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero n rewrite *-zeroʳ n = refl
*-comm (suc m) n rewrite *-suc n m | *-comm m n = refl

∸-zero : ∀ (n : ℕ) → zero ∸ n ≡ zero
∸-zero zero = refl
∸-zero (suc n) = refl

-- _∸_ : ℕ → ℕ → ℕ
-- n     - zero = n
-- zero  - suc m = zero
-- suc n - suc m = n - m

∸-|-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-|-assoc m zero p = refl
∸-|-assoc zero (suc n) p rewrite ∸-zero p = refl
∸-|-assoc (suc m) (suc n) p rewrite ∸-|-assoc m n p = refl


-- _^_ : ℕ → ℕ → ℕ
-- x ^ zero  = 1
-- x ^ suc n = x * x ^ n

^-distribˡ-|-* : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distribˡ-|-* m zero p rewrite +-identityʳ (m ^ p) = refl
^-distribˡ-|-* m (suc n) p rewrite ^-distribˡ-|-* m n p | *-assoc m (m ^ n) (m ^ p) = refl


^-distribʳ-|-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distribʳ-|-* m n zero = refl
^-distribʳ-|-* m n (suc p)
  rewrite ^-distribʳ-|-* m n p
  | *-assoc m n ((m ^ p) * (n ^ p))
  | sym (*-assoc n (m ^ p) (n ^ p))
  | *-comm n (m ^ p)
  | *-assoc (m ^ p) n (n ^ p)
  | sym (*-assoc m (m ^ p) (n * (n ^ p))) = refl

1^ : (n : ℕ) → 1 ^ n ≡ 1
1^ zero = refl
1^ (suc n) rewrite 1^ n = refl

^-*-assoc : (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
^-*-assoc m zero p = 1^ p
^-*-assoc m (suc n) p
  rewrite ^-distribʳ-|-* m (m ^ n) p
  | ^-*-assoc m n p
  | sym (^-distribˡ-|-* m p (n * p)) = refl


data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = inc b O

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc n) = inc (to n)

from : Bin → ℕ
from ⟨⟩ = zero
from (n O) = from n * 2
from (n I) = (from n * 2) + 1

inc-suc : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
inc-suc ⟨⟩ = refl
inc-suc (b O) rewrite
    +-suc (from b * 2) zero
  | +-identityʳ (from b * 2) = refl
inc-suc (b I) rewrite
    inc-suc b
  | sym (+-identityʳ (from b * 2))
  | sym (+-suc (from b * 2) zero)
  | +-identityʳ (from b * 2) = refl

{-
from-to-identity : ∀ (b : Bin) → to (from b) ≡ b
from-to-identity ⟨⟩ = {!!} -- Goal: (⟨⟩ O) ≡ ⟨⟩
from-to-identity (b O) = {!!}
from-to-identity (b I) = {!!}

Counterexample:

  to (from ⟨⟩ 0 1 0 1) ≡ ⟨⟩ 1 0 1
-}

from∘to : ∀ (n : ℕ) → from (to n) ≡ n
from∘to zero = refl
from∘to (suc n) rewrite
    inc-suc (to n)
  | from∘to n = refl

-- Standard Library
import Data.Nat.Properties using (+-assoc; +-identityʳ; +-suc; +-comm)
