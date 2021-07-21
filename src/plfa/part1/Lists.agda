module plfa.part1.Lists where

----------------------
-- Imports

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import Level using (Level)
open import plfa.part1.Isomorphism using (_≃_; _⇔_; extensionality)

----------------------
-- Lists

data List (A : Set) : Set where
  []  : List A -- pronunced nil
  _∷_ : A → List A → List A -- pronounced cons/constructor

infixr 5 _∷_

-- As we’ve seen, parameterised types can be translated to indexed types.
-- The definition above is equivalent to the following:
data List′ : Set → Set where
  []′  : ∀ {A : Set} → List′ A
  _∷′_ : ∀ {A : Set} → A → List′ A → List′ A

_ : List ℕ
_ = _∷_ {ℕ} 0 (_∷_ {ℕ} 1 (_∷_ {ℕ} 2 ([] {ℕ})))

-- Including the pragma:
{-# BUILTIN LIST List #-}
-- tells Agda that the type List corresponds to the Haskell type list, and the constructors [] and _∷_ correspond to nil and cons respectively, allowing a more efficient representation of lists.

-----------------------------------
-- List syntax

-- We can write lists more conveniently by introducing the following definitions:

pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []

-- This is our first use of pattern declarations.
-- For instance, the third line tells us that [ x , y , z ] is equivalent to x ∷ y ∷ z ∷ [],
-- and permits the former to appear either in a pattern on the left-hand side of an equation,
-- or a term on the right-hand side of an equation.

-----------------------------
-- Append

infixr 5 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[]       ++ ys  =  ys
(x ∷ xs) ++ ys  =  x ∷ (xs ++ ys)

-- Appending two lists requires time linear in the number of elements in the first list.

_ : [ 0 , 1 , 2 ] ++ [ 3 , 4 ] ≡ [ 0 , 1 , 2 , 3 , 4 ]
_ =
  begin
    0 ∷ 1 ∷ 2 ∷ [] ++ 3 ∷ 4 ∷ []
  ≡⟨⟩
    0 ∷ (1 ∷ 2 ∷ [] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ (2 ∷ [] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ 2 ∷ ([] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []
  ∎

-------------------------------------
-- Reasoning about append

++-assoc : ∀ {A : Set} (xs ys zs : List A)
  → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs =
  begin
    ([] ++ ys) ++ zs
  ≡⟨⟩
    ys ++ zs
  ≡⟨⟩
    [] ++ (ys ++ zs)
  ∎
++-assoc (x ∷ xs) ys zs =
  begin
    (x ∷ xs ++ ys) ++ zs
  ≡⟨⟩
    (x ∷ (xs ++ ys)) ++ zs
  ≡⟨⟩
    x ∷ ((xs ++ ys) ++ zs)
  ≡⟨ cong (x ∷_) (++-assoc xs ys zs) ⟩
    x ∷ (xs ++ (ys ++ zs))
  ≡⟨⟩
    (x ∷ xs) ++ (ys ++ zs)
  ∎

{-
Recall that Agda supports sections. Applying cong (x ∷_) promotes the inductive hypothesis:

  (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)

to the equality:

  x ∷ ((xs ++ ys) ++ zs) ≡ x ∷ (xs ++ (ys ++ zs))

which is needed in the proof.
-}

++-identityˡ : ∀ {A : Set} (xs : List A) → [] ++ xs ≡ xs
++-identityˡ xs =
  begin
    [] ++ xs
  ≡⟨⟩
    xs
  ∎

++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] =
  begin
    [] ++ []
  ≡⟨⟩
    []
  ∎
++-identityʳ (x ∷ xs) =
  begin
    (x ∷ xs) ++ []
  ≡⟨⟩
    x ∷ (xs ++ [])
  ≡⟨ cong (x ∷_) (++-identityʳ xs) ⟩
    x ∷ xs
  ∎

-- As we will see later, these three properties establish that _++_ and [] form a monoid over lists.

------------------------------------
-- Length

length : ∀ {A : Set} → List A → ℕ
length []        =  zero
length (x ∷ xs)  =  suc (length xs)

_ : length [ 0 , 1 , 2 ] ≡ 3
_ =
  begin
    length (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    suc (length (1 ∷ 2 ∷ []))
  ≡⟨⟩
    suc (suc (length (2 ∷ [])))
  ≡⟨⟩
    suc (suc (suc (length {ℕ} [])))
  ≡⟨⟩
    suc (suc (suc zero))
  ∎
-- In the second-to-last line, we cannot write simply length [] but must instead write length {ℕ} [].
-- Since [] has no elements, Agda has insufficient information to infer the implicit parameter.

-- Computing the length of a list requires time linear in the number of elements in the list.

--------------------------------------
-- Reasoning about length

length-++ : ∀ {A : Set} (xs ys : List A)
  → length (xs ++ ys) ≡ length xs + length ys
length-++ {A} [] ys =
  begin
    length ([] ++ ys)
  ≡⟨⟩
    length ys
  ≡⟨⟩
    zero + length ys
  ≡⟨⟩
    length {A} [] + length ys
  ∎
length-++ (x ∷ xs) ys =
  begin
    length ((x ∷ xs) ++ ys)
  ≡⟨⟩
    suc (length (xs ++ ys))
  ≡⟨ cong suc (length-++ xs ys) ⟩
    suc (length xs + length ys)
  ≡⟨⟩
    length (x ∷ xs) + length ys
  ∎

------------------------------------
-- Reverse

reverse : ∀ {A : Set} → List A → List A
reverse []        =  []
reverse (x ∷ xs)  =  reverse xs ++ [ x ]

_ : reverse [ 0 , 1 , 2 ] ≡ [ 2 , 1 , 0 ]
_ =
  begin
    reverse (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    reverse (1 ∷ 2 ∷ []) ++ [ 0 ]
  ≡⟨⟩
    (reverse (2 ∷ []) ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    ((reverse [] ++ [ 2 ]) ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    (([] ++ [ 2 ]) ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    (([] ++ 2 ∷ []) ++ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    (2 ∷ [] ++ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    2 ∷ ([] ++ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    (2 ∷ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    2 ∷ (1 ∷ [] ++ 0 ∷ [])
  ≡⟨⟩
    2 ∷ 1 ∷ ([] ++ 0 ∷ [])
  ≡⟨⟩
    2 ∷ 1 ∷ 0 ∷ []
  ≡⟨⟩
    [ 2 , 1 , 0 ]
  ∎

-- Reversing a list in this way takes time quadratic in the length of the list.
-- This is because reverse ends up appending lists of lengths 1, 2, up to n - 1,
-- where n is the length of the list being reversed, append takes time linear in
-- the length of the first list, and the sum of the numbers up to n - 1 is n * (n - 1) / 2

----------------------------------------------
-- Exercises

reverse-++-distrib : ∀ {A : Set} (xs ys : List A)
  → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-distrib {A} [] ys =
  begin
    reverse ([] ++ ys)
  ≡⟨⟩
    reverse ys
  ≡⟨ sym (++-identityʳ (reverse ys)) ⟩
    reverse ys ++ []
  ≡⟨⟩
    reverse ys ++ reverse []
  ∎
reverse-++-distrib (x ∷ xs) ys =
  begin
    reverse ((x ∷ xs) ++ ys)
  ≡⟨⟩
    reverse (x ∷ (xs ++ ys))
  ≡⟨⟩
    (reverse (xs ++ ys)) ++ [ x ]
  ≡⟨ cong (_++ [ x ]) (reverse-++-distrib xs ys) ⟩
    (reverse ys ++ reverse xs) ++ [ x ]
  ≡⟨ ++-assoc (reverse ys) (reverse xs) ([ x ]) ⟩
    reverse ys ++ (reverse xs ++ [ x ])
  ≡⟨⟩
    reverse ys ++ (reverse (x ∷ xs))
  ≡⟨⟩
    reverse ys ++ reverse (x ∷ xs)
  ∎

-- A function is an involution if when applied twice it acts as the identity function. Show that reverse is an involution:

reverse-involutive : ∀ {A : Set} (xs : List A)
  → reverse (reverse xs) ≡ xs
reverse-involutive [] = refl
reverse-involutive (x ∷ xs) =
  begin
    reverse (reverse (x ∷ xs))
  ≡⟨⟩
    reverse ((reverse xs) ++ [ x ])
  ≡⟨ reverse-++-distrib (reverse xs) [ x ] ⟩
    reverse [ x ] ++ reverse (reverse xs)
  ≡⟨⟩
    [ x ] ++ reverse (reverse xs)
  ≡⟨ cong ([ x ] ++_) (reverse-involutive xs) ⟩
    (x ∷ []) ++ xs
  ≡⟨⟩
    x ∷ ([] ++ xs)
  ≡⟨⟩
    x ∷ xs
  ∎

---------------------------------
-- Faster reverse

shunt : ∀ {A : Set} → List A → List A → List A
shunt []       ys  =  ys
shunt (x ∷ xs) ys  =  shunt xs (x ∷ ys)
-- The second argument actually becomes larger,
-- but this is not a problem because the argument on which we recurse becomes smaller.

shunt-reverse : ∀ {A : Set} (xs ys : List A)
  → shunt xs ys ≡ reverse xs ++ ys
shunt-reverse [] ys =
  begin
    shunt [] ys
  ≡⟨⟩
    ys
  ≡⟨⟩
    reverse [] ++ ys
  ∎
shunt-reverse (x ∷ xs) ys =
  begin
    shunt (x ∷ xs) ys
  ≡⟨⟩
    shunt xs (x ∷ ys)
  ≡⟨ shunt-reverse xs (x ∷ ys) ⟩
    reverse xs ++ (x ∷ ys)
  ≡⟨⟩
    reverse xs ++ ([ x ] ++ ys)
  ≡⟨ sym (++-assoc (reverse xs) [ x ] ys) ⟩
    (reverse xs ++ [ x ]) ++ ys
  ≡⟨⟩
    reverse (x ∷ xs) ++ ys
  ∎

-- Generalising on an auxiliary argument, which becomes larger as the argument on which we recurse
-- or induct becomes smaller, is a common trick. It belongs in your quiver of arrows, ready to slay the right problem.

reverse′ : ∀ {A : Set} → List A → List A
reverse′ xs = shunt xs []

reverses : ∀ {A : Set} (xs : List A)
  → reverse′ xs ≡ reverse xs
reverses xs =
  begin
    reverse′ xs
  ≡⟨⟩
    shunt xs []
  ≡⟨ shunt-reverse xs [] ⟩
    reverse xs ++ []
  ≡⟨ ++-identityʳ (reverse xs) ⟩
    reverse xs
  ∎

_ : reverse′ [ 0 , 1 , 2 ] ≡ [ 2 , 1 , 0 ]
_ =
  begin
    reverse′ (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    shunt (0 ∷ 1 ∷ 2 ∷ []) []
  ≡⟨⟩
    shunt (1 ∷ 2 ∷ []) (0 ∷ [])
  ≡⟨⟩
    shunt (2 ∷ []) (1 ∷ 0 ∷ [])
  ≡⟨⟩
    shunt [] (2 ∷ 1 ∷ 0 ∷ [])
  ≡⟨⟩
    2 ∷ 1 ∷ 0 ∷ []
  ∎

-- Now the time to reverse a list is linear in the length of the list.

---------------------------------------------
-- Map

-- Map is an example of a higher-order function,
-- one which takes a function as an argument or returns a function as a result:

map : ∀ {A B : Set} → (A → B) → List A → List B
map f []        =  []
map f (x ∷ xs)  =  f x ∷ map f xs

_ : map suc [ 0 , 1 , 2 ] ≡ [ 1 , 2 , 3 ]
_ =
  begin
    map suc (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    suc 0 ∷ map suc (1 ∷ 2 ∷ [])
  ≡⟨⟩
    suc 0 ∷ suc 1 ∷ map suc (2 ∷ [])
  ≡⟨⟩
    suc 0 ∷ suc 1 ∷ suc 2 ∷ map suc []
  ≡⟨⟩
    suc 0 ∷ suc 1 ∷ suc 2 ∷ []
  ≡⟨⟩
    1 ∷ 2 ∷ 3 ∷ []
  ∎

sucs : List ℕ → List ℕ
sucs = map suc

_ : sucs [ 0 , 1 , 2 ] ≡ [ 1 , 2 , 3 ]
_ =
  begin
    sucs [ 0 , 1 , 2 ]
  ≡⟨⟩
    map suc [ 0 , 1 , 2 ]
  ≡⟨⟩
    [ 1 , 2 , 3 ]
  ∎

-----------------------------
-- Exercises

map-compose : ∀ {A B C : Set} {f : A → B} {g : B → C}
  → map (g ∘ f) ≡ map g ∘ map f
map-compose = extensionality map-compose′
  where
    map-compose′ : ∀ {A B C : Set} {f : A → B} {g : B → C} (xs : List A)
      → map (g ∘ f) xs ≡ (map g ∘ map f) xs
    map-compose′ [] = refl
    map-compose′ {A} {B} {C} {f} {g} (x ∷ xs) rewrite map-compose′ {A} {B} {C} {f} {g} xs = refl

map-++-distribute : ∀ {A B : Set} (f : A → B) (xs ys : List A)
  → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-distribute _ [] ys = refl
map-++-distribute f (x ∷ xs) ys =
  begin
    map f ((x ∷ xs) ++ ys)
  ≡⟨⟩
    map f (x ∷ (xs ++ ys))
  ≡⟨⟩
    f x ∷ map f (xs ++ ys)
  ≡⟨ cong ((f x) ∷_) (map-++-distribute f xs ys) ⟩
    f x ∷ map f xs ++ map f ys
  ≡⟨⟩
    map f (x ∷ xs) ++ map f ys
  ∎

data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  node : Tree A B → B → Tree A B → Tree A B

map-Tree : ∀ {A B C D : Set} → (A → C) → (B → D) → Tree A B → Tree C D
map-Tree f g (leaf a) = leaf (f a)
map-Tree f g (node l b r) = node (map-Tree f g l) (g b) (map-Tree f g r)


--------------------------------
-- Fold

foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr _⊗_ e []        =  e
foldr _⊗_ e (x ∷ xs)  =  x ⊗ foldr _⊗_ e xs

_ : foldr _+_ 0 [ 1 , 2 , 3 , 4 ] ≡ 10
_ =
  begin
    foldr _+_ 0 (1 ∷ 2 ∷ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    1 + foldr _+_ 0 (2 ∷ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    1 + (2 + foldr _+_ 0 (3 ∷ 4 ∷ []))
  ≡⟨⟩
    1 + (2 + (3 + foldr _+_ 0 (4 ∷ [])))
  ≡⟨⟩
    1 + (2 + (3 + (4 + foldr _+_ 0 [])))
  ≡⟨⟩
    1 + (2 + (3 + (4 + 0)))
  ∎
sum : List ℕ → ℕ
sum = foldr _+_ 0

_ : sum [ 1 , 2 , 3 , 4 ] ≡ 10
_ =
  begin
    sum [ 1 , 2 , 3 , 4 ]
  ≡⟨⟩
    foldr _+_ 0 [ 1 , 2 , 3 , 4 ]
  ≡⟨⟩
    10
  ∎

-- In general, a data type with n constructors will have a corresponding fold function that takes n arguments.

-------------------------
-- Exercises

product : List ℕ → ℕ
product = foldr _*_ 1

_ : product [ 1 , 2 , 3 , 4 ] ≡ 24
_ =
  begin
    product [ 1 , 2 , 3 , 4 ]
  ≡⟨⟩
    foldr _*_ 1 [ 1 , 2 , 3 , 4 ]
  ≡⟨⟩
    1 * 2 * 3 * 4 * 1
  ≡⟨⟩
    24
  ∎

foldr-++ : ∀ {A B : Set} (_⊗_ : A → B → B) (e : B) (xs ys : List A)
  → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs
foldr-++ _ e [] ys = refl
foldr-++ _⊗_ e (x ∷ xs) ys =
  begin
    foldr _⊗_ e ((x ∷ xs) ++ ys)
  ≡⟨⟩
    foldr _⊗_ e (x ∷ (xs ++ ys))
  ≡⟨⟩
    x ⊗ (foldr _⊗_ e (xs ++ ys))
  ≡⟨ cong (x ⊗_) (foldr-++ _⊗_ e xs ys)⟩
    x ⊗ (foldr _⊗_ (foldr _⊗_ e ys) xs)
  ≡⟨⟩
    foldr _⊗_ (foldr _⊗_ e ys) (x ∷ xs)
  ∎
-- Notice the difference between _⊗_ and ⊗

foldr-∷ : ∀ {A : Set} (xs : List A)
  → foldr _∷_ [] xs ≡ xs
foldr-∷ [] = refl
foldr-∷ (x ∷ xs) rewrite foldr-∷ xs = refl

-- foldr-++-lemma : ∀ {A : Set} (xs ys : List A)
--   → xs ++ ys ≡ foldr _∷_ ys xs
-- foldr-++-lemma [] ys = refl
-- foldr-++-lemma (x ∷ xs) ys rewrite foldr-++-lemma xs ys = refl

foldr-++-lemma : ∀ {A : Set} (xs ys : List A)
  → xs ++ ys ≡ foldr _∷_ ys xs
foldr-++-lemma xs ys =
  begin
    xs ++ ys
  ≡⟨ sym (foldr-∷ (xs ++ ys)) ⟩
    foldr _∷_ [] (xs ++ ys)
  ≡⟨ foldr-++ _∷_ [] xs ys ⟩
    foldr _∷_ (foldr _∷_ [] ys) xs
  ≡⟨ cong (λ{e → foldr _∷_ e xs}) (foldr-∷ ys) ⟩
    foldr _∷_ ys xs
  ∎

map-is-foldr : ∀ {A B : Set} {f : A → B}
  → map f ≡ foldr (λ x xs → f x ∷ xs) []
map-is-foldr = extensionality map-is-foldr′
  where
    map-is-foldr′ : ∀ {A B : Set} {f : A → B} (xs : List A)
      → map f xs ≡ foldr (λ x xs → f x ∷ xs) [] xs
    map-is-foldr′ [] = refl
    map-is-foldr′ {f = f} (x ∷ xs) = cong (f x ∷_) (map-is-foldr′ xs)

fold-Tree : ∀ {A B C : Set} → (A → C) → (C → B → C → C) → Tree A B → C
fold-Tree f _⊗_ (leaf x) = f x
fold-Tree f _⊗_ (node l x r) = _⊗_ (fold-Tree f _⊗_ l) x (fold-Tree f _⊗_ r)

map-is-fold-Tree : ∀ {A B C D : Set} {f : A → C} {g : B → D}
  → map-Tree f g ≡ fold-Tree (λ x → leaf (f x)) (λ l x r → node l (g x) r)
map-is-fold-Tree = extensionality map-is-fold-Tree′
  where
    map-is-fold-Tree′ : ∀ {A B C D : Set} {f : A → C} {g : B → D} (t : Tree A B)
      → map-Tree f g t ≡ fold-Tree (λ x → leaf (f x)) (λ l x r → node l (g x) r) t
    map-is-fold-Tree′ (leaf x) = refl
    map-is-fold-Tree′ {g = g} (node l x r) = cong₂ (λ l r → node l (g x) r) (map-is-fold-Tree′ l) (map-is-fold-Tree′  r)

downFrom : ℕ → List ℕ
downFrom zero = []
downFrom (suc n) = n ∷ downFrom n

_ : downFrom 3 ≡ [ 2 , 1 , 0 ]
_ = refl

-- Prove that the sum of the numbers (n - 1) + ⋯ + 0 is equal to n * (n ∸ 1) / 2:
--
-- sum (downFrom n) * 2 ≡ n * (n ∸ 1)
--
-- TODO
-- TODO
-- TODO

------------------------------------
-- Monoids

record IsMonoid {A : Set} (_⊗_ : A → A → A) (e : A) : Set where
  field
    assoc : ∀ (x y z : A) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
    identityˡ : ∀ (x : A) → e ⊗ x ≡ x
    identityʳ : ∀ (x : A) → x ⊗ e ≡ x

open IsMonoid

+-monoid : IsMonoid _+_ 0
+-monoid =
  record
    { assoc = +-assoc
    ; identityˡ = +-identityˡ
    ; identityʳ = +-identityʳ
    }

*-monoid : IsMonoid _*_ 1
*-monoid =
  record
    { assoc = *-assoc
    ; identityˡ = *-identityˡ
    ; identityʳ = *-identityʳ
    }

++-monoid : ∀ {A : Set} → IsMonoid {List A} _++_ []
++-monoid =
  record
    { assoc = ++-assoc
    ; identityˡ = ++-identityˡ
    ; identityʳ = ++-identityʳ
    }

foldr-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs : List A) (y : A) → foldr _⊗_ y xs ≡ foldr _⊗_ e xs ⊗ y
foldr-monoid _⊗_ e ⊗-monoid [] y =
  begin
    foldr _⊗_ y []
  ≡⟨⟩
    y
  ≡⟨ sym (identityˡ ⊗-monoid y) ⟩
    (e ⊗ y)
  ≡⟨⟩
    (foldr _⊗_ e []) ⊗ y
  ∎
foldr-monoid _⊗_ e ⊗-monoid (x ∷ xs) y =
  begin
    foldr _⊗_ y (x ∷ xs)
  ≡⟨⟩
    x ⊗ (foldr _⊗_ y xs)
  ≡⟨ cong (x ⊗_) (foldr-monoid _⊗_ e ⊗-monoid xs y) ⟩
    x ⊗ (foldr _⊗_ e xs ⊗ y)
  ≡⟨ sym (assoc ⊗-monoid x (foldr _⊗_ e xs) y) ⟩
    (x ⊗ foldr _⊗_ e xs) ⊗ y
  ≡⟨⟩
    foldr _⊗_ e (x ∷ xs) ⊗ y
  ∎


-- postulate
--   foldr-++ : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) (xs ys : List A) →
--     foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs

foldr-monoid-++ : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs ys : List A) → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
foldr-monoid-++ _⊗_ e monoid-⊗ xs ys =
  begin
    foldr _⊗_ e (xs ++ ys)
  ≡⟨ foldr-++ _⊗_ e xs ys ⟩
    foldr _⊗_ (foldr _⊗_ e ys) xs
  ≡⟨ foldr-monoid _⊗_ e monoid-⊗ xs (foldr _⊗_ e ys) ⟩
    foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
  ∎

--------------------
-- Exercises

-- foldr _⊗_ e [ x , y , z ]  =  x ⊗ (y ⊗ (z ⊗ e))
-- foldl _⊗_ e [ x , y , z ]  =  ((e ⊗ x) ⊗ y) ⊗ z

foldl : ∀ {A B : Set} → (B → A → B) → B → List A → B
foldl _⊗_ e [] = e
foldl _⊗_ e (x ∷ xs) = foldl _⊗_ (e ⊗ x) xs

foldl-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A)
  → IsMonoid _⊗_ e
  → ∀ (xs : List A) (y : A) → y ⊗ foldl _⊗_ e xs ≡ foldl _⊗_ y xs
foldl-monoid _⊗_ e monoid-⊗ [] y rewrite identityʳ monoid-⊗ y = refl
foldl-monoid _⊗_ e monoid-⊗ (x ∷ xs) y =
  begin
    y ⊗ foldl _⊗_ e (x ∷ xs)
  ≡⟨⟩
    y ⊗ foldl _⊗_ (e ⊗ x) xs
  ≡⟨ cong (λ σ → y ⊗ foldl _⊗_ σ xs ) (identityˡ monoid-⊗ x) ⟩
    y ⊗ foldl _⊗_ x xs
  ≡⟨ cong (y ⊗_) (sym (foldl-monoid _⊗_ e monoid-⊗ xs x)) ⟩
    y ⊗ (x ⊗ foldl _⊗_ e xs)
  ≡⟨⟩
    y ⊗ (x ⊗ foldl _⊗_ e xs)
  ≡⟨ sym (assoc monoid-⊗ y x (foldl _⊗_ e xs)) ⟩
    (y ⊗ x) ⊗ foldl _⊗_ e xs
  ≡⟨ foldl-monoid _⊗_ e monoid-⊗ xs (y ⊗ x) ⟩
    foldl _⊗_ (y ⊗ x) xs
  ≡⟨⟩
    foldl _⊗_ y (x ∷ xs)
  ∎

foldr-monoid-foldl : ∀ {A : Set} (_⊗_ : A → A → A) (e : A)
  → IsMonoid _⊗_ e
  → ∀ (xs : List A) → foldr _⊗_ e xs ≡ foldl _⊗_ e xs
foldr-monoid-foldl _⊗_ e monoid-⊗ [] = refl
foldr-monoid-foldl _⊗_ e monoid-⊗ (x ∷ xs) =
  begin
    foldr _⊗_ e (x ∷ xs)
  ≡⟨⟩
    x ⊗ foldr _⊗_ e xs
  ≡⟨ cong (x ⊗_) (foldr-monoid-foldl _⊗_ e monoid-⊗ xs) ⟩
    x ⊗ (foldl _⊗_ e xs)
  ≡⟨ foldl-monoid _⊗_ e monoid-⊗ xs x ⟩
    foldl _⊗_ x xs
  ≡⟨ cong (λ e₁ → foldl _⊗_ e₁ xs) (sym (identityˡ monoid-⊗ x)) ⟩
    foldl _⊗_ (e ⊗ x) xs
  ≡⟨⟩
    foldl _⊗_ e (x ∷ xs)
  ∎

--------------------------------------------------
-- All

-- Predicate All P holds if predicate P is satisfied by every element of a list:

data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : ∀ {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)

-- Agda uses types to disambiguate whether the constructor is building a list or evidence that All P holds.

_ : All (_≤ 2) [ 0 , 1 , 2 ]
_ = z≤n ∷ s≤s z≤n ∷ s≤s (s≤s z≤n) ∷ []

-- Here _∷_ and [] are the constructors of All P rather than of List A.

-- One might wonder whether a pattern such as [_,_,_] can be used to construct values of type All as well as type List,
-- since both use the same constructors. Indeed it can, so long as both types are in scope when the pattern is declared.

----------------------------------------------
-- Any

-- Predicate Any P holds if predicate P is satisfied by some element of a list:

data Any {A : Set} (P : A → Set) : List A → Set where
  here  : ∀ {x : A} {xs : List A} → P x → Any P (x ∷ xs)
  there : ∀ {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)

-- For example, we can define list membership as follows:

infix 4 _∈_ _∉_

_∈_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∉ xs = ¬ (x ∈ xs)

_ : 0 ∈ [ 0 , 1 , 0 , 2 ]
_ = here refl

_ : 0 ∈ [ 0 , 1 , 0 , 2 ]
_ = there (there (here refl))

not-in : 3 ∉ [ 0 , 1 , 0 , 2 ]
not-in (here ())
not-in (there (here ()))
not-in (there (there (here ())))
not-in (there (there (there (here ()))))
not-in (there (there (there (there ()))))

-- The five occurrences of () attest to the fact that there is no
-- possible evidence for 3 ≡ 0, 3 ≡ 1, 3 ≡ 0, 3 ≡ 2, and 3 ∈ [], respectively.

-------------------------------------------
-- All and append

All-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  All P (xs ++ ys) ⇔ (All P xs × All P ys)
All-++-⇔ xs ys =
  record
    { to       =  to xs ys
    ; from     =  from xs ys
    }
  where

  to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
    All P (xs ++ ys) → (All P xs × All P ys)
  to [] ys Pys = ⟨ [] , Pys ⟩
  to (x ∷ xs) ys (Px ∷ Pxs++ys) with to xs ys Pxs++ys
  ... | ⟨ Pxs , Pys ⟩ = ⟨ Px ∷ Pxs , Pys ⟩

  from : ∀ { A : Set} {P : A → Set} (xs ys : List A) →
    All P xs × All P ys → All P (xs ++ ys)
  from [] ys ⟨ [] , Pys ⟩ = Pys
  from (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩ =  Px ∷ from xs ys ⟨ Pxs , Pys ⟩

----------------
-- Exercises

Any-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  Any P (xs ++ ys) ⇔ (Any P xs ⊎ Any P ys)
Any-++-⇔ xs ys =
  record
    { to = to xs ys
    ; from = from xs ys
    }
  where

  to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
    Any P (xs ++ ys) → (Any P xs ⊎ Any P ys)
  to [] ys Pys = inj₂ Pys
  to (x ∷ xs) ys (here Px) = inj₁ (here Px)
  to (x ∷ xs) ys (there Pxs++ys) with to xs ys Pxs++ys
  ... | (inj₁ Pxs) = inj₁ (there Pxs)
  ... | (inj₂ Pys) = inj₂ Pys

  from : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
    (Any P xs ⊎ Any P ys) → Any P (xs ++ ys)
  from [] ys (inj₂ Pys) = Pys
  from (x ∷ xs) ys (inj₁ (here Px)) = here Px
  from (x ∷ xs) ys (inj₁ (there Pxs)) = there (from xs ys (inj₁ Pxs))
  from (x ∷ xs) ys (inj₂ Pys) = there (from xs ys (inj₂ Pys))

All-++-≃ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  All P (xs ++ ys) ≃ (All P xs × All P ys)
All-++-≃ xs ys =
  record
    { to       =  to xs ys
    ; from     =  from xs ys
    ; from∘to  =  from∘to xs ys
    ; to∘from  =  to∘from xs ys
    }
  where

  to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
    All P (xs ++ ys) → (All P xs × All P ys)
  to [] ys Pys = ⟨ [] , Pys ⟩
  to (x ∷ xs) ys (Px ∷ Pxs++ys) with to xs ys Pxs++ys
  ... | ⟨ Pxs , Pys ⟩ = ⟨ Px ∷ Pxs , Pys ⟩

  from : ∀ { A : Set} {P : A → Set} (xs ys : List A) →
    All P xs × All P ys → All P (xs ++ ys)
  from [] ys ⟨ [] , Pys ⟩ = Pys
  from (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩ =  Px ∷ from xs ys ⟨ Pxs , Pys ⟩

  from∘to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
    ∀ (Pxs++ys : All P (xs ++ ys)) → from xs ys (to xs ys Pxs++ys) ≡ Pxs++ys
  from∘to [] ys Pxs++ys = refl
  from∘to (x ∷ xs) ys (x₁ ∷ Pxs++ys) = cong (x₁ ∷_) (from∘to xs ys Pxs++ys)

  to∘from : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
    ∀ (Pxs×Pys : (All P xs × All P ys)) → to xs ys (from xs ys Pxs×Pys) ≡ Pxs×Pys
  to∘from [] ys ⟨ [] , snd ⟩ = refl
  to∘from (x ∷ xs) ys ⟨ x₁ ∷ fst , snd ⟩ rewrite to∘from xs ys ⟨ fst , snd ⟩ = refl

-- Exercise ¬Any⇔All¬ (recommended)

-- Show that Any and All satisfy a version of De Morgan’s Law:

¬Any⇔All¬ : ∀ {A : Set} {P : A → Set} (xs : List A)
  → (¬_ ∘ Any P) xs ⇔ All (¬_ ∘ P) xs
¬Any⇔All¬ xs =
  record
    { to   = to xs
    ; from = from xs
    }
  where

  -- Can you see why it is important that here _∘_ is generalised to arbitrary levels,
  -- as described in the section on universe polymorphism?

  to : ∀ {A : Set} {P : A → Set} (xs : List A)
    → (¬_ ∘ Any P) xs → All (¬_ ∘ P) xs
  to [] ¬AnyP = []
  to (x ∷ xs) ¬AnyP = (λ Px → ¬AnyP (here Px)) ∷ to xs (λ Pxs → ¬AnyP (there Pxs))

  from : ∀ {A : Set} {P : A → Set} (xs : List A)
    → All (¬_ ∘ P) xs → (¬_ ∘ Any P) xs
  from [] [] ()
  from (x ∷ xs) (¬Px ∷ all) (here Px) = ¬Px Px
  from (x ∷ xs) (_ ∷ ¬Pxs) (there Pxs) = (from xs ¬Pxs) Pxs

-- Do we also have the following?
--
--   (¬_ ∘ All P) xs ⇔ Any (¬_ ∘ P) xs
--
-- If so, prove; if not, explain why.

Any¬→¬All : ∀ {A : Set} {P : A → Set} (xs : List A) →
  Any (¬_ ∘ P) xs → (¬_ ∘ All P) xs
Any¬→¬All (x ∷ xs) (here ¬Px) (Px ∷ all) = ¬Px Px
Any¬→¬All (_ ∷ xs) (there Any¬xs) (_ ∷ all) = (Any¬→¬All xs Any¬xs) all

-- ¬All→Any¬ : ∀ {A : Set} {P : A → Set} (xs : List A) →
--   (¬_ ∘ All P) xs → Any (¬_ ∘ P) xs
-- ¬All→Any¬ [] ¬All-xs = ?
-- ¬All→Any¬ (x ∷ xs) ¬All-xs = ?

-- ¬Any≃All¬ : ∀ {A : Set} {P : A → Set} (xs : List A)
--   → (¬_ ∘ Any P) xs ≃ All (¬_ ∘ P) xs
-- ¬Any≃All¬ xs =
--   record
--     { to      = to xs
--     ; from    = from xs
--     ; from∘to = from∘to xs
--     ; to∘from = to∘from xs
--     }
--   where

--   to : ∀ {A : Set} {P : A → Set} (xs : List A)
--     → (¬_ ∘ Any P) xs → All (¬_ ∘ P) xs
--   to [] ¬AnyP = []
--   to (x ∷ xs) ¬AnyP = (λ Px → ¬AnyP (here Px)) ∷ to xs (λ Pxs → ¬AnyP (there Pxs))

--   from : ∀ {A : Set} {P : A → Set} (xs : List A)
--     → All (¬_ ∘ P) xs → (¬_ ∘ Any P) xs
--   from [] [] ()
--   from (x ∷ xs) (¬Px ∷ all) (here Px) = ¬Px Px
--   from (x ∷ xs) (_ ∷ ¬Pxs) (there Pxs) = (from xs ¬Pxs) Pxs

--   from∘to : ∀ {A : Set} {P : A → Set} (xs : List A)
--     → ∀ (x : (¬_ ∘ Any P) xs) → from xs (to xs x) ≡ x
--   from∘to = {!!}

--   to∘from : ∀ {A : Set} {P : A → Set} (xs : List A)
--     → ∀ (x : All (¬_ ∘ P) xs) → to xs (from xs x) ≡ x
--   to∘from = {!!}

All-∀ : ∀ {A : Set} {P : A → Set} (xs : List A)
  → All P xs ⇔ (∀ {x} → x ∈ xs → P x)
All-∀ xs =
  record
    { to   = to xs
    ; from = from xs
    }
  where

  to : ∀ {A : Set} {P : A → Set} (xs : List A)
    → All P xs → (∀ {x} → x ∈ xs → P x)
  to [] [] ()
  to (x ∷ xs) (Px ∷ all) (here refl) = Px
  to (x ∷ xs) (Px ∷ Pxs) (there x₁∈xs) = (to xs Pxs) x₁∈xs

  from : ∀ {A : Set} {P : A → Set} (xs : List A)
    → (∀ {x} → x ∈ xs → P x) → All P xs
  from [] x∈xs = []
  from (x ∷ xs) x∈xs = x∈xs (here refl) ∷ from xs (λ x₁∈xs₁ → x∈xs (there x₁∈xs₁))


Any-∃ : ∀ {A : Set} {P : A → Set} (xs : List A)
  → Any P xs ⇔ ∃[ x ] (x ∈ xs × P x)
Any-∃ xs =
  record
    { to   = to xs
    ; from = from xs
    }
  where

  to : ∀ {A : Set} {P : A → Set} (xs : List A)
    → Any P xs → ∃[ x ] (x ∈ xs × P x)
  to (x ∷ xs) (here Px) = ⟨ x , ⟨ here refl , Px ⟩ ⟩
  to (x ∷ xs) (there Pxs) with to xs Pxs
  ... | ⟨ x′ , ⟨ x′∈xs , Px′ ⟩ ⟩ = ⟨ x′ , ⟨ there x′∈xs , Px′ ⟩ ⟩

  from : ∀ {A : Set} {P : A → Set} (xs : List A)
    → ∃[ x ] (x ∈ xs × P x) → Any P xs
  from (x ∷ xs) ⟨ x′ , ⟨ here refl , Px′ ⟩ ⟩ = here Px′
  from (x ∷ xs) ⟨ x′ , ⟨ there x′∈xs , Px′ ⟩ ⟩ = there (from xs ⟨ x′ , ⟨ x′∈xs , Px′ ⟩ ⟩)

-------------------------------------------
-- Decidability of All

-- If we consider a predicate as a function that yields a boolean,
-- it is easy to define an analogue of All, which returns true if a given predicate
-- returns true for every element of a list:

all : ∀ {A : Set} → (A → Bool) → List A → Bool
all p  =  foldr _∧_ true ∘ map p

-- As one would hope, if we replace booleans by decidables there is again an analogue of All.
-- First, return to the notion of a predicate P as a function of type A → Set,
-- taking a value x of type A into evidence P x that a property holds for x.
-- Say that a predicate P is decidable if we have a function that for a given x can decide P x:

Decidable : ∀ {A : Set} → (A → Set) → Set
Decidable {A} P  =  ∀ (x : A) → Dec (P x)

-- Then if predicate P is decidable, it is also decidable whether every element of a list satisfies the predicate:

All? : ∀ {A : Set} {P : A → Set} → Decidable P → Decidable (All P)
All? P? [] =  yes []
All? P? (x ∷ xs) with P? x   | All? P? xs
...                 | yes Px | yes Pxs     =  yes (Px ∷ Pxs)
...                 | no ¬Px | _           =  no λ{ (Px ∷ Pxs) → ¬Px Px   }
...                 | _      | no ¬Pxs     =  no λ{ (Px ∷ Pxs) → ¬Pxs Pxs }

any : ∀ {A : Set} → (A → Bool) → List A → Bool
any p = foldr _∨_ false ∘ map p

Any? : ∀ {A : Set} {P : A → Set} → Decidable P → Decidable (Any P)
Any? P? [] = no (λ ())
Any? P? (x ∷ xs) with P? x   | Any? P? xs
...                 | yes Px | _          = yes (here Px)
...                 | _      | yes Pxs    = yes (there Pxs)
...                 | no ¬Px | no ¬Pxs    = no λ{ (here Px) → ¬Px Px ; (there Pxs) → ¬Pxs Pxs}

-- The relation merge holds when two lists merge to give a third list.

data merge {A : Set} : (xs ys zs : List A) → Set where

  [] :
      --------------
      merge [] [] []

  left-∷ : ∀ {x xs ys zs}
    → merge xs ys zs
      --------------------------
    → merge (x ∷ xs) ys (x ∷ zs)

  right-∷ : ∀ {y xs ys zs}
    → merge xs ys zs
      --------------------------
    → merge xs (y ∷ ys) (y ∷ zs)

_ : merge [ 1 , 4 ] [ 2 , 3 ] [ 1 , 2 , 3 , 4 ]
_ = left-∷ (right-∷ (right-∷ (left-∷ [])))

-- Given a decidable predicate and a list, we can split the list into two lists that merge to give the original list,
-- where all elements of one list satisfy the predicate, and all elements of the other do not satisfy the predicate.

-- Define the following variant of the traditional filter function on lists, which given a decidable predicate
-- and a list returns a list of elements that satisfy the predicate and a list of elements that don’t,
-- with their corresponding proofs.

split : ∀ {A : Set} {P : A → Set} (P? : Decidable P) (zs : List A)
  → ∃[ xs ] ∃[ ys ] ( merge xs ys zs × All P xs × All (¬_ ∘ P) ys )
split P? [] = ⟨ [] , ⟨ [] , ⟨ [] , ⟨ [] , [] ⟩ ⟩ ⟩ ⟩
split P? (z ∷ zs) with P? z   | split P? zs
...                  | yes Px | ⟨ xs , ⟨ ys , ⟨ merge , ⟨ all , all¬ ⟩ ⟩ ⟩ ⟩ = ⟨ z ∷ xs , ⟨ ys , ⟨ left-∷ merge , ⟨ Px ∷ all , all¬ ⟩ ⟩ ⟩ ⟩
...                  | no ¬Px | ⟨ xs , ⟨ ys , ⟨ merge , ⟨ all , all¬ ⟩ ⟩ ⟩ ⟩ = ⟨ xs , ⟨ z ∷ ys , ⟨ right-∷ merge , ⟨ all , ¬Px ∷ all¬ ⟩ ⟩ ⟩ ⟩

-------------------------------------------
-- Standard Library

-- Definitions similar to those in this chapter can be found in the standard library:

{-

import Data.List using (List; _++_; length; reverse; map; foldr; downFrom)
import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.Any using (Any; here; there)
import Data.List.Membership.Propositional using (_∈_)
import Data.List.Properties
  using (reverse-++-commute; map-compose; map-++-commute; foldr-++)
  renaming (mapIsFold to map-is-foldr)
import Algebra.Structures using (IsMonoid)
import Relation.Unary using (Decidable)
import Relation.Binary using (Decidable)

-}

-- The standard library version of IsMonoid differs from the one given here,
-- in that it is also parameterised on an equivalence relation.

-- Both Relation.Unary and Relation.Binary define a version of Decidable,
-- one for unary relations (as used in this chapter where P ranges over unary predicates)
-- and one for binary relations (as used earlier, where _≤_ ranges over a binary relation).
