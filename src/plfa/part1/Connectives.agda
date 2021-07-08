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
