module plfa.part1.Connectives where

{-
Correspondence between connectives of logic and data types,
a principle known as Propositions as Types:

  - conjunction is product,
  - disjunction is sum,
  - true is unit type,
  - false is empty type,
  - implication is function space.
-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import plfa.part1.Isomorphism using (_≃_; _≲_; extensionality; _⇔_)
open plfa.part1.Isomorphism.≃-Reasoning

------------------------------------------------------
-- Conjunction is product

-- Given two propositions A and B, the conjunction A × B holds if both A holds and B holds.
--
-- We formalise this idea by declaring a suitable record type:

data _×_ (A B : Set) : Set where

  ⟨_,_⟩ :
      A
    → B
      -----
    → A × B
infixr 2 _×_
-- Thus, m ≤ n × n ≤ p parses as (m ≤ n) × (n ≤ p).

-- Evidence that A × B holds is of the form ⟨ M , N ⟩,
-- where M provides evidence that A holds and N provides evidence that B holds.
--
-- Given evidence that A × B holds, we can conclude that either A holds or B holds:

proj₁ : ∀ {A B : Set}
  → A × B
    -----
  → A
proj₁ ⟨ x , y ⟩ = x

proj₂ : ∀ {A B : Set}
  → A × B
    -----
  → B
proj₂ ⟨ x , y ⟩ = y

-- Other terminology refers to ⟨_,_⟩ as introducing a conjunction,
-- and to proj₁ and proj₂ as eliminating a conjunction; indeed,
-- the former is sometimes given the name ×-I and the latter two the names ×-E₁ and ×-E₂
--
-- An introduction rule describes under what conditions we say
-- the connective holds — how to define the connective.
--
-- An elimination rule describes what we may conclude when
-- the connective holds — how to use the connective.

η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ x , y ⟩ = refl
-- The pattern matching on the left-hand side is essential,
-- since replacing w by ⟨ x , y ⟩ allows both sides of the propositional equality to simplify to the same term.

-- Alternatively:

record _×′_ (A B : Set) : Set where
  constructor ⟨_,_⟩′
  field
    proj₁′ : A
    proj₂′ : B
open _×′_
-- The constructor declaration allows us to write ⟨ M , N ⟩′ in place of the record construction.

-- The data type _x_ and the record type _×′_ behave similarly.
-- One difference is that for data types we have to prove η-equality, but for record types, η-equality holds by definition.
-- While proving η-×′, we do not have to pattern match on w to know that η-equality holds:

η-×′ : ∀ {A B : Set} (w : A ×′ B) → ⟨ proj₁′ w , proj₂′ w ⟩′ ≡ w
η-×′ w = refl

-- It can be very convenient to have η-equality definitionally, and so the standard library defines _×_ as a record type.

-- Given two types A and B, we refer to A × B as the product of A and B.
-- In set theory, it is also sometimes called the Cartesian product, and in computing it corresponds to a record type.

-- Among other reasons for calling it the product, note that if type A has m distinct members,
-- and type B has n distinct members, then the type A × B has m * n distinct members.

-- For instance, consider a type Bool with two members, and a type Tri with three members:

data Bool : Set where
  true  : Bool
  false : Bool

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

-- Then the type Bool × Tri has six members:
-- ⟨ true  , aa ⟩    ⟨ true  , bb ⟩    ⟨ true ,  cc ⟩
-- ⟨ false , aa ⟩    ⟨ false , bb ⟩    ⟨ false , cc ⟩

×-count : Bool × Tri → ℕ
×-count ⟨ true  , aa ⟩  =  1
×-count ⟨ true  , bb ⟩  =  2
×-count ⟨ true  , cc ⟩  =  3
×-count ⟨ false , aa ⟩  =  4
×-count ⟨ false , bb ⟩  =  5
×-count ⟨ false , cc ⟩  =  6

-- In particular, product is commutative and associative up to isomorphism.

×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm =
  record
    { to       =  λ{ ⟨ x , y ⟩ → ⟨ y , x ⟩ }
    ; from     =  λ{ ⟨ y , x ⟩ → ⟨ x , y ⟩ }
    ; from∘to  =  λ{ ⟨ x , y ⟩ → refl }
    ; to∘from  =  λ{ ⟨ y , x ⟩ → refl }
    }

{-
Being commutative is different from being commutative up to isomorphism. Compare the two statements:

m * n ≡ n * m
A × B ≃ B × A

In the first case, we might have that m is 2 and n is 3, and both m * n and n * m are equal to 6.

In the second case, we might have that A is Bool and B is Tri, and Bool × Tri is not the same as Tri × Bool.

But there is an isomorphism between the two types. For instance, ⟨ true , aa ⟩, which is a member of the former,
corresponds to ⟨ aa , true ⟩, which is a member of the latter.
-}

×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc =
  record
    { to      = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → ⟨ x , ⟨ y , z ⟩ ⟩ }
    ; from    = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → ⟨ ⟨ x , y ⟩ , z ⟩ }
    ; from∘to = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → refl }
    ; to∘from = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → refl }
    }

{-
Being associative is not the same as being associative up to isomorphism. Compare the two statements:

(m * n) * p ≡ m * (n * p)
(A × B) × C ≃ A × (B × C)

For example, the type (ℕ × Bool) × Tri is not the same as ℕ × (Bool × Tri).

But there is an isomorphism between the two types.

For instance ⟨ ⟨ 1 , true ⟩ , aa ⟩, which is a member of the former,
corresponds to ⟨ 1 , ⟨ true , aa ⟩ ⟩, which is a member of the latter.
-}

open _⇔_

⇔≃× : ∀ {A B : Set} → (A ⇔ B) ≃ ((A → B) × (B → A))
⇔≃× =
  record
    { to      = λ{ A⇔B → ⟨ to A⇔B , from A⇔B ⟩}
    ; from    = λ{⟨ A→B , B→A ⟩ → record { to = A→B; from = B→A }}
    ; from∘to = λ{ x → refl }
    ; to∘from = λ{ ⟨ A→B , B→A ⟩ → refl }
    }

--------------------------------------------------------
-- Truth is unit

-- Truth ⊤ always holds. We formalise this idea by declaring a suitable record type:
data ⊤ : Set where
  tt :
    --
    ⊤

-- There is an introduction rule, but no elimination rule.
-- Given evidence that ⊤ holds, there is nothing more of interest we can conclude.
-- Since truth always holds, knowing that it holds tells us nothing new.

η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl
-- The pattern matching on the left-hand side is essential.
-- Replacing w by tt allows both sides of the propositional equality to simplify to the same term.

--  Alternatively, we can declare truth as an empty record:

record ⊤′ : Set where
  constructor tt′
-- The record construction record {} corresponds to the term tt.
-- The constructor declaration allows us to write tt′.

-- As with the product, the data type ⊤ and the record type ⊤′ behave similarly,
-- but η-equality holds by definition for the record type.
--
-- While proving η-⊤′, we do not have to pattern match on w—Agda knows it is equal to tt′:

η-⊤′ : ∀ (w : ⊤′) → tt′ ≡ w
η-⊤′ w = refl

-- Agda knows that any value of type ⊤′ must be tt′, so any
-- time we need a value of type ⊤′, we can tell Agda to figure it out:

truth′ : ⊤′
truth′ = _

-- We refer to ⊤ as the unit type.
-- And, indeed, type ⊤ has exactly one member, tt.

⊤-count : ⊤ → ℕ
⊤-count tt = 1

-- Unit is the identity of product up to isomorphism(⊤ × Bool ≢ Bool)

⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-identityˡ =
  record
    { to      = λ{ ⟨ tt , x ⟩ → x }
    ; from    = λ{ x → ⟨ tt , x ⟩ }
    ; from∘to = λ{ ⟨ tt , x ⟩ → refl }
    ; to∘from = λ{ x → refl }
    }

-- Right identity follows from commutativity of product and left identity:

⊤-identityʳ : ∀ {A : Set} → (A × ⊤) ≃ A
⊤-identityʳ {A} =
  ≃-begin
    (A × ⊤)
  ≃⟨ ×-comm ⟩
    (⊤ × A)
  ≃⟨ ⊤-identityˡ ⟩
    A
  ≃-∎

--------------------------------------------
-- Disjunction is sum

-- Given two propositions A and B, the disjunction A ⊎ B holds if either A holds or B holds.

data _⊎_ (A B : Set) : Set where

  inj₁ :
      A
      -----
    → A ⊎ B

  inj₂ :
      B
      -----
    → A ⊎ B

infixr 1 _⊎_ -- Thus, A × C ⊎ B × C parses as (A × C) ⊎ (B × C).

-- Given evidence that A → C and B → C both hold,
-- then given evidence that A ⊎ B holds we can conclude that C holds:

case-⊎ : ∀ {A B C : Set}
  → (A → C)
  → (B → C)
  → A ⊎ B
    -----------
  → C
case-⊎ f g (inj₁ x) = f x
case-⊎ f g (inj₂ y) = g y

-- When inj₁ and inj₂ appear on the right-hand side of an equation we refer to them as *constructors,*
-- and when they appear on the left-hand side we refer to them as *destructors*.
--
-- We also refer to case-⊎ as a destructor, since it plays a similar role.
--
-- Other terminology refers to inj₁ and inj₂ as introducing a disjunction,
-- and to case-⊎ as eliminating a disjunction; indeed the former are sometimes given
-- the names ⊎-I₁ and ⊎-I₂ and the latter the name ⊎-E.

-- Applying the destructor to each of the constructors is the identity:

η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ y) = refl

-- More generally, we can also throw in an arbitrary function from a disjunction:

uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) →
  case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ x) = refl
uniq-⊎ h (inj₂ y) = refl
-- The pattern matching on the left-hand side is essential.

-- Given two types A and B, we refer to A ⊎ B as the sum of A and B.
-- In set theory, it is also sometimes called the disjoint union, and
-- in computing it corresponds to a variant record type.
--
-- Among other reasons for calling it the sum, note that if type A has m distinct members,
-- and type B has n distinct members, then the type A ⊎ B has m + n distinct members.

⊎-count : Bool ⊎ Tri → ℕ
⊎-count (inj₁ true)   =  1
⊎-count (inj₁ false)  =  2
⊎-count (inj₂ aa)     =  3
⊎-count (inj₂ bb)     =  4
⊎-count (inj₂ cc)     =  5

-- Sum on types also shares a property with sum on numbers in that it is commutative and associative up to isomorphism.

⊎-comm : ∀ {A B : Set} → A ⊎ B ≃ B ⊎ A
⊎-comm =
  record
    { to      = λ{ (inj₁ a) → inj₂ a ; (inj₂ b) → inj₁ b }
    ; from    = λ{ (inj₁ b) → inj₂ b ; (inj₂ a) → inj₁ a }
    ; from∘to = λ{ (inj₁ a) → refl ; (inj₂ b) → refl }
    ; to∘from = λ{ (inj₁ b) → refl ; (inj₂ a) → refl }
    }

⊎-assoc : ∀ {A B C : Set} → (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
⊎-assoc =
  record
    { to      = λ{ (inj₁ (inj₁ a)) → inj₁ a
                 ; (inj₁ (inj₂ b)) → (inj₂ ∘ inj₁) b
                 ; (inj₂ c) → (inj₂ ∘ inj₂) c
                 }
    ; from    = λ{ (inj₁ a) → (inj₁ ∘ inj₁) a
                 ; (inj₂ (inj₁ b)) → (inj₁ ∘ inj₂) b
                 ; (inj₂ (inj₂ c)) → inj₂ c
                 }
    ; from∘to = λ{ (inj₁ (inj₁ a)) → refl
                 ; (inj₁ (inj₂ b)) → refl
                 ; (inj₂ c) → refl
                 }
    ; to∘from = λ{ (inj₁ a) → refl
                 ; (inj₂ (inj₁ b)) → refl
                 ; (inj₂ (inj₂ c)) → refl
                 }
    }

--------------------------------------------------------
-- False is empty

data ⊥ : Set where

-- There is no possible evidence that ⊥ holds.

-- Dual to ⊤, for ⊥ there is no introduction rule but an elimination rule.
-- Since false never holds, knowing that it holds tells us we are in a paradoxical situation.
--
-- Given evidence that ⊥ holds, we might conclude anything! This is a basic principle of logic,
-- known in medieval times by the Latin phrase ex falso, and known to children through phrases
-- such as “if pigs had wings, then I’d be the Queen of Sheba”. We formalise it as follows:

-- The nullary case of case-⊎ is ⊥-elim:

⊥-elim : ∀ {A : Set}
  → ⊥
    --
  → A
⊥-elim ()

-- This is our first use of the absurd pattern ().
-- Here since ⊥ is a type with no members, we indicate that
-- it is never possible to match against a value of this type by using the pattern ().

-- The nullary case of uniq-⊎ is uniq-⊥,
-- which asserts that ⊥-elim is equal to any arbitrary function from ⊥:

uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ h ()
-- Using the absurd pattern asserts there are no possible values for w, so the equation holds trivially.

-- We refer to ⊥ as the empty type. And, indeed, type ⊥ has no members.
-- For example, the following function enumerates all possible arguments of type ⊥:

⊥-count : ⊥ → ℕ
⊥-count ()

-- For numbers, zero is the identity of addition.
-- Correspondingly, empty is the identity of sums up to isomorphism.

⊥-identityˡ : ∀ {A : Set} → ⊥ ⊎ A ≃ A
⊥-identityˡ =
  record
    { to = λ{ (inj₁ ()); (inj₂ a) → a }
    ; from = λ{ a → inj₂ a }
    ; from∘to = λ{ (inj₁ ()); (inj₂ a) → refl }
    ; to∘from = λ{ a → refl }
    }

⊥-identityʳ : ∀ {A : Set} → A ⊎ ⊥ ≃ A
⊥-identityʳ {A} =
  ≃-begin
    (A ⊎ ⊥)
  ≃⟨ ⊎-comm ⟩
    (⊥ ⊎ A)
  ≃⟨ ⊥-identityˡ {A} ⟩
    A
  ≃-∎
------------------------------------------
-- Implication is function

{-
Given two propositions A and B, the implication A → B holds
if whenever A holds then B must also hold.

We formalise implication using the function type,
which has appeared throughout this book.

Evidence that A → B holds is of the form:

  λ (x : A) → N

where N is a term of type B containing as a free variable x of type A.

Given a term L providing evidence that A → B holds, and a term M providing evidence
that A holds, the term L M provides evidence that B holds.

In other words, evidence that A → B holds is a function that converts
evidence that A holds into evidence that B holds.
-}

→-elim : ∀ {A B : Set}
  → (A → B)
  → A
    -------
  → B
→-elim L M = L M

{-
In medieval times, this rule was known by the name modus ponens.
It corresponds to function application.

Defining a function, with a named definition or a lambda abstraction,
is referred to as introducing a function, while applying a function
is referred to as eliminating the function.

Elimination followed by introduction is the identity:
-}

η-→ : ∀ {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ f = refl

{-
Implication binds less tightly than any other operator.
Thus, A ⊎ B → B ⊎ A parses as (A ⊎ B) → (B ⊎ A).

Given two types A and B, we refer to A → B as the function space from A to B.
It is also sometimes called the exponential, with B raised to the A power.
Among other reasons for calling it the exponential, note that
if type A has m distinct members, and type B has n distinct members,
then the type A → B has nᵐ distinct members.

λ{true → aa; false → aa}  λ{true → aa; false → bb}  λ{true → aa; false → cc}
λ{true → bb; false → aa}  λ{true → bb; false → bb}  λ{true → bb; false → cc}
λ{true → cc; false → aa}  λ{true → cc; false → bb}  λ{true → cc; false → cc}

For example, the following function enumerates all possible arguments of the type Bool → Tri:
-}

→-count : (Bool → Tri) → ℕ
→-count f with f true | f false
...          | aa     | aa      =   1
...          | aa     | bb      =   2
...          | aa     | cc      =   3
...          | bb     | aa      =   4
...          | bb     | bb      =   5
...          | bb     | cc      =   6
...          | cc     | aa      =   7
...          | cc     | bb      =   8
...          | cc     | cc      =   9

{-
Corresponding to the law

  (p ^ n) ^ m  ≡  p ^ (n * m)

we have the isomorphism

  A → (B → C)  ≃  (A × B) → C

Both types can be viewed as functions that given evidence
that A holds and evidence that B holds can return evidence that C holds.

This isomorphism sometimes goes by the name currying. The proof of the right inverse requires extensionality:
-}

currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
currying =
  record
    { to      =  λ{ f → λ{ ⟨ x , y ⟩ → f x y }}
    ; from    =  λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ }}}
    ; from∘to =  λ{ f → refl }
    ; to∘from =  λ{ g → extensionality λ{ ⟨ x , y ⟩ → refl }}
    }

{-
Corresponding to the law

  p ^ (n + m) = (p ^ n) * (p ^ m)

we have the isomorphism:

  (A ⊎ B) → C  ≃  (A → C) × (B → C)
-}

→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-distrib-⊎ =
  record
    { to      = λ{ f → ⟨ f ∘ inj₁ , f ∘ inj₂ ⟩ }
    ; from    = λ{ ⟨ g , h ⟩ → λ{ (inj₁ x) → g x ; (inj₂ y) → h y } }
    ; from∘to = λ{ f → extensionality λ{ (inj₁ x) → refl ; (inj₂ y) → refl } }
    ; to∘from = λ{ ⟨ g , h ⟩ → refl }
    }

{-
Corresponding to the law

  (p * n) ^ m = (p ^ m) * (n ^ m)

we have the isomorphism:

  A → B × C  ≃  (A → B) × (A → C)
-}

→-distrib-× : ∀ {A B C : Set} → (A → B × C) ≃ (A → B) × (A → C)
→-distrib-× =
  record
    { to      = λ{ f → ⟨ proj₁ ∘ f , proj₂ ∘ f ⟩ }
    ; from    = λ{ ⟨ g , h ⟩ → λ x → ⟨ g x , h x ⟩ }
    ; from∘to = λ{ f → extensionality λ{ x → η-× (f x) } }
    ; to∘from = λ{ ⟨ g , h ⟩ → refl }
    }

-------------------------------------------------
-- Distribution

-- Products distribute over sum, up to isomorphism.
-- The code to validate this fact is similar in structure to our previous results:

×-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
×-distrib-⊎ =
  record
    { to      = λ{ ⟨ inj₁ x , z ⟩ → (inj₁ ⟨ x , z ⟩)
                 ; ⟨ inj₂ y , z ⟩ → (inj₂ ⟨ y , z ⟩)
                 }
    ; from    = λ{ (inj₁ ⟨ x , z ⟩) → ⟨ inj₁ x , z ⟩
                 ; (inj₂ ⟨ y , z ⟩) → ⟨ inj₂ y , z ⟩
                 }
    ; from∘to = λ{ ⟨ inj₁ x , z ⟩ → refl
                 ; ⟨ inj₂ y , z ⟩ → refl
                 }
    ; to∘from = λ{ (inj₁ ⟨ x , z ⟩) → refl
                 ; (inj₂ ⟨ y , z ⟩) → refl
                 }
    }

-- Sums do not distribute over products up to isomorphism, but it is an embedding:

-- We have an embedding rather than an isomorphism because
-- the `from` function must discard either z or z′ in this case.
⊎-distrib-× : ∀ {A B C : Set} → (A × B) ⊎ C ≲ (A ⊎ C) × (B ⊎ C)
⊎-distrib-× =
  record
    { to      = λ{ (inj₁ ⟨ x , y ⟩) → ⟨ inj₁ x , inj₁ y ⟩
                 ; (inj₂ z)         → ⟨ inj₂ z , inj₂ z ⟩
                 }
    ; from    = λ{ ⟨ inj₁ x , inj₁ y ⟩ → (inj₁ ⟨ x , y ⟩)
                 ; ⟨ inj₁ x , inj₂ z ⟩ → (inj₂ z)
                 ; ⟨ inj₂ z , _      ⟩ → (inj₂ z)
                 }
    ; from∘to = λ{ (inj₁ ⟨ x , y ⟩) → refl
                 ; (inj₂ z)         → refl
                 }
    }

{-

In the usual approach to logic, both of the distribution laws are given
as equivalences, where each side implies the other:

  A × (B ⊎ C) ⇔ (A × B) ⊎ (A × C)
  A ⊎ (B × C) ⇔ (A ⊎ B) × (A ⊎ C)

But when we consider the functions that provide evidence for these implications,
then the first corresponds to an isomorphism while the second only corresponds
to an embedding, revealing a sense in which one of these laws is
“more true” than the other.
-}

-- Show that the following property holds:

⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
⊎-weak-× ⟨ inj₁ a , _ ⟩ = inj₁ a
⊎-weak-× ⟨ inj₂ b , c ⟩ = inj₂ ⟨ b , c ⟩
-- This is called a weak distributive law.

--  Show that a disjunct of conjuncts implies a conjunct of disjuncts:

⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
⊎×-implies-×⊎ (inj₁ ⟨ a , b ⟩) = ⟨ inj₁ a , inj₁ b ⟩
⊎×-implies-×⊎ (inj₂ ⟨ c , d ⟩) = ⟨ inj₂ c ,  inj₂ d ⟩

-- Does the converse hold? If so, prove; if not, give a counterexample.

-- ×⊎-implies-⊎× : ∀ {A B C D : Set} → (A ⊎ C) × (B ⊎ D) → (A × B) ⊎ (C × D)
-- ×⊎-implies-⊎× (⟨ inj₁ a , inj₁ b ⟩) = inj₁ ⟨ a , b ⟩
-- ×⊎-implies-⊎× (⟨ inj₁ a , inj₂ d ⟩) = ???

-- It is easy to see that if A holds and C holds
-- does not imply that A×B holds or C×D holds.

-------------------------------------------
-- Standard library

import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
import Data.Unit using (⊤; tt)
import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
import Data.Empty using (⊥; ⊥-elim)
import Function.Equivalence using (_⇔_)

-- The standard library constructs pairs with _,_ whereas we use ⟨_,_⟩.
--
-- The former makes it convenient to build triples or larger tuples from pairs,
-- permitting a , b , c to stand for (a , (b , c)).
--
-- But it conflicts with other useful notations,
-- such as [_,_] to construct a list of two elements in Chapter Lists
-- and Γ , A to extend environments in Chapter DeBruijn.
--
-- The standard library _⇔_ is similar to ours, but
-- the one in the standard library is less convenient,
-- since it is parameterised with respect to an arbitrary notion of equivalence.
