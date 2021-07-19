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
    x ∷ (xs ++ ys) ++ zs
  ≡⟨⟩
    x ∷ ((xs ++ ys) ++ zs)
  ≡⟨ cong (x ∷_) (++-assoc xs ys zs) ⟩
    x ∷ (xs ++ (ys ++ zs))
  ≡⟨⟩
    x ∷ xs ++ (ys ++ zs)
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

-- Demonstrating both these equations is left as an exercise:
--
-- foldr _∷_ [] xs ≡ xs
--
-- xs ++ ys ≡ foldr _∷_ ys xs

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
  → map-Tree f g ≡ fold-Tree {A} {B} {Tree C D} (λ x → leaf (f x)) (λ l x r → node l (g x) r)
map-is-fold-Tree = extensionality map-is-fold-Tree′
  where
    map-is-fold-Tree′ : ∀ {A B C D : Set} {f : A → C} {g : B → D} (t : Tree A B)
      → map-Tree f g t ≡ fold-Tree {A} {B} {Tree C D} (λ x → leaf (f x)) (λ l x r → node l (g x) r) t
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

------------------------------------
-- Monoids
