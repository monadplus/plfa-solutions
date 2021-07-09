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
