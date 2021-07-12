{-# OPTIONS --allow-unsolved-metas #-}
module plfa.part1.Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; +-identityʳ; *-comm; +-suc)

data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ}
      --------
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}
    → m ≤ n
      -------------
    → suc m ≤ suc n

infix 4 _≤_

{-
  z≤n -----
      0 ≤ 2

 s≤s -------
      1 ≤ 3
s≤s ---------
      2 ≤ 4
-}
_ : 2 ≤ 4
_ = s≤s (s≤s z≤n)

-- { } are called /implicit arguments/ and are not needed to be written explicitly.
-- We can write z≤n leaving n implicit. Similarly, we can write s<s m≤n

_ : 2 ≤ 4
_ = s≤s {1} {3} (s≤s {0} {2} (z≤n {2}))

_ : 2 ≤ 4
_ = s≤s {m = 1} {n = 3} (s≤s {m = 0} {n = 2} (z≤n {n = 2}))

_ : 2 ≤ 4
_ = s≤s {n = 3} (s≤s {n = 2} z≤n)

-- It is not permitted to swap implicit arguments, even when named.

-- We can ask Agda to use the same inference to try and infer an explicit term, by writing _
+-identityʳ′ : ∀ {m : ℕ} → m + zero ≡ m
+-identityʳ′ = +-identityʳ _

--------------------------------------
-- Decidability

-- Given two numbers, it is straightforward to compute whether or not the first is less than or equal
-- to the second. We will return to this point in Chapter Decidable.

--------------------------------------
-- Inversion

inv-s≤s : ∀ {m n : ℕ}
  → suc m ≤ suc n
    -------------
  → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n
-- m≤n is a term with type m ≤ n
-- It is a common convention in Agda to derive a variable name by removing spaces from its type.

inv-z≤n : ∀ {m : ℕ}
  → m ≤ zero
    --------
  → m ≡ zero
inv-z≤n z≤n = refl

--------------------------------------
-- Properties of ordering relations

-- Reflexive
-- Transitive
-- Anti-symmetric: ∀ m n : m ≤ n ∧ n ≤ m ⟶ m ≡ n
-- Total: ∀ m n : m ≤ n ∨ n ≤ m

-- The relation ≤ satisfies all four.

-- Preorder: reflexive + transitive
-- Partial order: preorder + anti-symmetric
-- Total order: partial order + total


-- Give an example of a preorder that is not a partial order.
--
-- Reachbility in a directed graph:
--   where x ≤ y in the preorder if and only if there is a path from x to y in the directed graph
--
-- The relation defined by x ≤ y if f(x) ≤ f(y), where f is a function into some preorder.
--
-- The subtyping relations are usually preorders.


-- Give an example of a partial order that is not a total order.
--
-- Subset relation by inclusion (A ⊆ B)

--------------------------------------
-- Reflexivity

≤-refl : ∀ {n : ℕ}
    -----
  → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

--------------------------------------
-- Transitivity

≤-trans : ∀ {m n p : ℕ}
  → m ≤ n
  → n ≤ p
    -----
  → m ≤ p
≤-trans z≤n       _          =  z≤n
≤-trans (s≤s m≤n) (s≤s n≤p)  =  s≤s (≤-trans m≤n n≤p)

-- The technique of induction on evidence that a property holds
-- (e.g., inducting on evidence that m ≤ n) — rather than induction on values of which
-- the property holds (e.g., inducting on m) — will turn out to be immensely valuable, and one that we use often.

-- For me, explicit parameters proof is harder to read.
≤-trans′ : ∀ (m n p : ℕ)
  → m ≤ n
  → n ≤ p
    -----
  → m ≤ p
≤-trans′ zero    _       _       z≤n       _          =  z≤n
≤-trans′ (suc m) (suc n) (suc p) (s≤s m≤n) (s≤s n≤p)  =  s≤s (≤-trans′ m n p m≤n n≤p)

--------------------------------------
-- Anti-symmetry

-- Proof by induction over the evidence.
≤-antisym : ∀ {m n : ℕ}
  → m ≤ n
  → n ≤ m
    -----
  → m ≡ n
≤-antisym z≤n       z≤n        =  refl
≤-antisym (s≤s m≤n) (s≤s n≤m)  =  cong suc (≤-antisym m≤n n≤m)

-- The case for the constructor s≤s is impossible
-- because unification ended with a conflicting equation
--   suc n ≟ zero
-- Possible solution: remove the clause, or use an absurd pattern ().
-- when checking that the pattern s≤s n≤m has type n ≤ zero

--------------------------------------
-- Total

-- Datatype with parameters
data Total (m n : ℕ) : Set where

  forward :
      m ≤ n
      ---------
    → Total m n

  flipped :
      n ≤ m
      ---------
    → Total m n

-- Evidence that Total m n holds is either of the form forward m≤n or flipped n≤m,
-- where m≤n and n≤m are evidence of m ≤ n and n ≤ m respectively.

-- For those familiar with logic, the above definition could also be written as a disjunction.
-- Disjunctions will be introduced in Chapter Connectives.

data Total′ : ℕ → ℕ → Set where

  forward′ : ∀ {m n : ℕ}
    → m ≤ n
      ----------
    → Total′ m n

  flipped′ : ∀ {m n : ℕ}
    → n ≤ m
      ----------
    → Total′ m n

-- Unlike an indexed datatype, where the indexes can vary (as in zero ≤ n and suc m ≤ suc n),
-- in a parameterised datatype the parameters must always be the same (as in Total m n).

-- Parameterised declarations are shorter, easier to read,
-- and occasionally aid Agda’s termination checker, so we will
-- use them in preference to indexed types when possible.

≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero    n                         =  forward z≤n
≤-total (suc m) zero                      =  flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
...                        | forward m≤n  =  forward (s≤s m≤n)
...                        | flipped n≤m  =  flipped (s≤s n≤m)

-- with is equivalent to

≤-total′ : ∀ (m n : ℕ) → Total m n
≤-total′ zero    n        =  forward z≤n
≤-total′ (suc m) zero     =  flipped z≤n
≤-total′ (suc m) (suc n)  =  helper (≤-total′ m n)
  where
  helper : Total m n → Total (suc m) (suc n)
  helper (forward m≤n)  =  forward (s≤s m≤n)
  helper (flipped n≤m)  =  flipped (s≤s n≤m)

-- Any variables bound on the left-hand side of the preceding equation
-- (in this case, m and n) are in scope within the nested definition,
-- and any identifiers bound in the nested definition (in this case, helper)
-- are in scope in the right-hand side of the preceding equation.

≤-total″ : ∀ (m n : ℕ) → Total m n
≤-total″ m       zero                      =  flipped z≤n
≤-total″ zero    (suc n)                   =  forward z≤n
≤-total″ (suc m) (suc n) with ≤-total″ m n
...                        | forward m≤n   =  forward (s≤s m≤n)
...                        | flipped n≤m   =  flipped (s≤s n≤m)

--------------------------------------
-- Monotonicity

-- Is addition monotonic with regard to inequality?
-- ∀ {m n p q : ℕ} → m ≤ n → p ≤ q → m + p ≤ n + q

+-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    -------------
  → n + p ≤ n + q
+-monoʳ-≤ zero    p q p≤q  =  p≤q
+-monoʳ-≤ (suc n) p q p≤q  =  s≤s (+-monoʳ-≤ n p q p≤q)

-- Proving +-monoˡ-≤ without +-monoʳ-≤ is challenging.

+-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n  rewrite +-comm m p | +-comm n p  = +-monoʳ-≤ p m n m≤n

+-mono-≤ : ∀ {m n p q : ℕ}
  → m ≤ n
  → p ≤ q
    -------------
  → m + p ≤ n + q
+-mono-≤ {m} {n} {p} {q} m≤n p≤q = ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)

*-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    -------------
  → n * p ≤ n * q
*-monoʳ-≤ zero p q p≤q = z≤n
*-monoʳ-≤ (suc n) p q p≤q = +-mono-≤ p≤q (*-monoʳ-≤ n p q p≤q)

*-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m * p ≤ n * p
*-monoˡ-≤ m n p m≤n rewrite *-comm m p | *-comm n p = *-monoʳ-≤ p m n m≤n

*-mono-≤ : ∀ {m n p q : ℕ}
  → m ≤ n
  → p ≤ q
    -------------
  → m * p ≤ n * q
*-mono-≤ {m} {n} {p} {q} m≤n p≤q = ≤-trans (*-monoˡ-≤ m n p m≤n) (*-monoʳ-≤ n p q p≤q)

--------------------------------------
-- Strict inequality

data _<_ : ℕ → ℕ → Set where

  z<s : ∀ {n : ℕ}
      ------------
    → zero < suc n

  s<s : ∀ {m n : ℕ}
    → m < n
      -------------
    → suc m < suc n

infix 4 _<_

-- Irreflexive: n < n nevel holds
-- Transitive
-- Not total but trichotomy: ∀ m,n   m < n ∨ m ≡ n ∨ m > n
-- Monotonic w.r.t addition and multiplication

-- Irreflexivity requires negation, as does the fact that
-- the three cases in trichotomy are mutually exclusive,
-- so those points are deferred to Chapter Negation.

-- It is straightforward to show that suc m ≤ n implies m < n, and conversely.
-- One can then give an alternative derivation of the properties of strict inequality,
-- such as transitivity, by exploiting the corresponding properties of inequality.

<-trans : ∀ {m n p : ℕ}
  → m < n
  → n < p
     -----
  → m < p
<-trans z<s (s<s n<p) = z<s
<-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)

data Trichotomy (m n : ℕ) : Set where

  less :
      m < n
      -----
    → Trichotomy m n

  equal :
      n ≡ m
      -----
    → Trichotomy m n

  greater :
      n < m
      -----
    → Trichotomy m n


<-total : ∀ (m n : ℕ) → Trichotomy m n
<-total zero zero = equal refl
<-total zero (suc n) = less z<s
<-total (suc m) zero = greater z<s
<-total (suc m) (suc n) with <-total m n
...                      | less m<n = less (s<s m<n)
...                      | equal refl = equal refl
...                      | greater n<m = greater (s<s n<m)

+-monoʳ-< : ∀ (n p q : ℕ)
  -> p < q
     -------------
  -> n + p < n + q
+-monoʳ-< zero p q p<q = p<q
+-monoʳ-< (suc n) p q p<q = s<s (+-monoʳ-< n p q p<q)

+-monoˡ-< : ∀ (m n p : ℕ)
  → m < n
    -------------
  → m + p < n + p
+-monoˡ-< m n p m<n rewrite +-comm m p | +-comm n p = +-monoʳ-< p m n m<n

+-mono-< : ∀ (m n p q : ℕ)
  → m < n
  → p < q
     -------------
  → m + p < n + q
+-mono-< m n p q m<n p<q = <-trans (+-monoˡ-< m n p m<n) (+-monoʳ-< n p q p<q)

≤-iff-< : ∀ (m n : ℕ)
  → suc m ≤ n
     ---------
  → m < n
≤-iff-< zero (suc n) _ = z<s
≤-iff-< (suc m) (suc n) (s≤s p) = s<s (≤-iff-< m n p)

<-iff-≤ : ∀ (m n : ℕ)
  → m < n
     ---------
  → suc m ≤ n
<-iff-≤ zero (suc n) p = s≤s z≤n
<-iff-≤ (suc m) (suc n) (s<s p) = s≤s (<-iff-≤ m n p)

-- The reverse is not true
<-if-≤ : ∀ (m n : ℕ)
  → m < n
    -----
  → m ≤ n
<-if-≤ zero n m<n = z≤n
<-if-≤ (suc m) (suc n) (s<s m<n) = s≤s (<-if-≤ m n m<n)

<-trans-revisited : ∀ {m n p : ℕ}
  → m < n
  → n < p
     -----
  → m < p
<-trans-revisited {m} {n} {p} m<n n<p = ≤-iff-< m p (≤-trans (s≤s (<-if-≤ m n m<n)) (<-iff-≤ n p n<p))

--------------------------------------
-- Even and odd

-- Mutually recursive datatype

-- Agda requires identifiers defined before being used.

-- Overloeaded constructors: same constructor for different types.

data even : ℕ → Set
data odd  : ℕ → Set

data even where

  zero :
      ---------
      even zero

  suc  : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where

  suc  : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)

e+e≡e : ∀ {m n : ℕ}
  → even m
  → even n
    ------------
  → even (m + n)

o+e≡o : ∀ {m n : ℕ}
  → odd m
  → even n
    -----------
  → odd (m + n)

e+o≡o : ∀ {m n : ℕ}
  → even m
  → odd n
    -----------
  → odd (m + n)

e+e≡e zero     en  =  en
e+e≡e (suc om) en  =  suc (o+e≡o om en)

o+e≡o (suc em) en  =  suc (e+e≡e em en)

e+o≡o {m} {suc n} em (suc en) rewrite +-suc m n = suc (e+e≡e em en)

o+o≡e : ∀ {m n : ℕ}
  → odd m
  → odd n
  → even (m + n)
o+o≡e (suc em) on = suc (e+o≡o em on)

o+o≡e' : ∀ {m n : ℕ}
  → odd m
  → odd n
  → even (m + n)
o+o≡e' {suc m} {n} (suc em) on rewrite +-comm m n = suc (o+e≡o on em)


--------------------------------------
-- Bin

data Bin : Set where
  ∘ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

-- Leading one.
data One : Bin → Set where

  one :
      ---------
      One (∘ I)

  suc₀ : ∀ {b : Bin}
    → One b
      ---------
    → One (b O)

  suc₁ : ∀ {b : Bin}
    → One b
      ---------
    → One (b I)

-- Canonical bitstring: leading one or single zero.

data Can : Bin → Set where

  zero :
      ---------
      Can (∘ O)

  leading-one : ∀ {b : Bin}
    → One b
      -----
    → Can b

inc : Bin → Bin
inc ∘ = ∘ I
inc (b O) = b I
inc (b I) = inc b O

-- Show that increment preserves canonical bitstrings:

inc-can-one : ∀ {b : Bin}
  → One b
    -----------
  → One (inc b)
inc-can-one one = suc₀ one
inc-can-one (suc₀ b) = suc₁ b
inc-can-one (suc₁ b) = suc₀ (inc-can-one b)

inc-can : ∀ {b : Bin}
  → Can b
    -----------
  → Can (inc b)
inc-can zero = leading-one one
inc-can (leading-one one-p) = leading-one (inc-can-one one-p)

to : ℕ → Bin
to zero = ∘ O
to (suc n) = inc (to n)

-- Show that converting a natural to a bitstring always yields a canonical bitstring:

to-can : ∀ (n : ℕ)
  ------------
  → Can (to n)
to-can zero = zero
to-can (suc n) = inc-can (to-can n)

-- Show that converting a canonical bitstring to a natural and back is the identity

from : Bin → ℕ
from ∘ = zero
from (n O) = from n * 2
from (n I) = (from n * 2) + 1

one-≤-from : ∀ {b : Bin}
  → One b
    -----
  → 1 ≤ from b
one-≤-from one = s≤s z≤n
one-≤-from (suc₀ one-b) = *-mono-≤ (one-≤-from one-b) (s≤s z≤n)
one-≤-from (suc₁ one-b) = +-mono-≤ (*-mono-≤ (one-≤-from one-b) (s≤s z≤n)) z≤n

from-to-one : ∀ {b : Bin}
  → One b
    ---------------
  → to (from b) ≡ b
from-to-one one = refl
from-to-one (suc₀ one-b) = {!!}
-- Goal: to (from b * 2) ≡ (b O)
from-to-one (suc₁ one-b) = {!!}
-- Goal: to (from b * 2 + 1) ≡ (b I)

from-to-can : ∀ {b : Bin}
  → Can b
    ---------------
  → to (from b) ≡ b
from-to-can zero = refl
from-to-can (leading-one x) = from-to-one x

--------------------------------------
-- Standard Library

-- import Data.Nat using (_≤_; z≤n; s≤s)
-- import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-antisym; ≤-total;
--                                   +-monoʳ-≤; +-monoˡ-≤; +-mono-≤)
