module plfa.part1.Quantifiers where

----------------------------------------

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import plfa.part1.Isomorphism using (_≃_; extensionality)

----------------------------------------
-- Universals

-- We formalise universal quantification using the dependent function type

-- In general, given a variable x of type A and a proposition B x which contains x as a free variable,
-- the universally quantified proposition ∀ (x : A) → B x holds if for every term M of type A the proposition B M holds.
--
-- Here B M stands for the proposition B x with each free occurrence of x replaced by M.
--
-- Variable x appears free in B x but bound in ∀ (x : A) → B x.

-- Evidence that ∀ (x : A) → B x holds is of the form
--   λ (x : A) → N x
-- where N x is a term of type B x, and N x and B x both contain a free variable x of type A.
--
-- Given a term L providing evidence that ∀ (x : A) → B x holds,
-- and a term M of type A, the term L M provides evidence that B M holds.
--
-- In other words, evidence that ∀ (x : A) → B x holds is a function that converts a term M of type A
-- into evidence that B M holds.

-- Put another way, if we know that ∀ (x : A) → B x holds
-- and that M is a term of type A then we may conclude that B M holds:
∀-elim : ∀ {A : Set} {B : A → Set}
  → (L : ∀ (x : A) → B x)
  → (M : A)
    -----------------
  → B M
∀-elim L M = L M
-- As with →-elim, the rule corresponds to function application.

-- Functions arise as a special case of dependent functions,
-- where the range does not depend on a variable drawn from the domain.
--
-- When a function is viewed as evidence of implication, both its argument and result are viewed as evidence,
-- whereas when a dependent function is viewed as evidence of a universal, its argument is viewed
-- as an element of a data type and its result is viewed as evidence of a proposition that depends on the argument.
--
-- This difference is largely a matter of interpretation, since in Agda a value of a type
-- and evidence of a proposition are indistinguishable.

-- Dependent function types are sometimes referred to as dependent products,
-- because if A is a finite type with values x₁ , ⋯ , xₙ,
-- and if each of the types B x₁ , ⋯ , B xₙ has m₁ , ⋯ , mₙ distinct members,
-- then ∀ (x : A) → B x has m₁ * ⋯ * mₙ members.
--
-- Indeed, sometimes the notation ∀ (x : A) → B x is replaced by a notation such as
--   Π[ x ∈ A ] (B x)
-- where Π stands for product.
--
-- However, we will stick with the name dependent function, because (as we will see) dependent product is ambiguous.

------------------------------------------
-- Exercises

∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-distrib-× =
  record
    { to      = λ{ f → ⟨ (λ x → proj₁ (f x)) , (λ x → proj₂ (f x)) ⟩}
    ; from    = λ{ ⟨ f , g ⟩ → (λ x → ⟨ f x , g x ⟩)}
    ; from∘to = λ{f → refl}
    ; to∘from = λ{ ⟨ f , g ⟩ → refl}
    }
-- →-distrib-× : ∀ {A B C : Set} → (A → B × C) ≃ (A → B) × (A → C)
-- →-distrib-× =
--   record
--     { to      = λ{ f → ⟨ proj₁ ∘ f , proj₂ ∘ f ⟩ }
--     ; from    = λ{ ⟨ g , h ⟩ → λ x → ⟨ g x , h x ⟩ }
--     ; from∘to = λ{ f → extensionality λ{ x → η-× (f x) } }
--     ; to∘from = λ{ ⟨ g , h ⟩ → refl }
--     }

⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)  →  ∀ (x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ (inj₁ f) x = inj₁ (f x)
⊎∀-implies-∀⊎ (inj₂ g) x = inj₂ (g x)
-- Does the converse hold? If so, prove; if not, explain why.
--
-- It does not hold in intuistic logic since you need to know which side holds a priori
-- of the result of the application.
--
-- It may hold in classic logic with the Excluded Middle Theorem (∀ {A : Set} → A ⊎ ¬ A)
--
-- ∀⊎-implies-⊎∀ : ∀ {A : Set} {B C : A → Set} →
--   (∀ (x : A) → B x ⊎ C x) → (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)
-- ∀⊎-implies-⊎∀ = ?

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

postulate
  extensionality′ : ∀ {A : Set} {B : A → Set} {f g : (x : A) → B x}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

≃-Tri : ∀ {B : Tri → Set} →
  (∀ (x : Tri) → B x) ≃ (B aa × B bb × B cc)
≃-Tri =
  record
    { to      = λ f → ⟨ f aa , ⟨ f bb , f cc ⟩ ⟩
    ; from    = λ (⟨ Baa , ⟨ Bbb , Bcc ⟩ ⟩) → λ{ aa → Baa ; bb → Bbb ; cc → Bcc }
    ; from∘to = λ f → extensionality′ λ{ aa → refl ; bb → refl ; cc → refl }
    ; to∘from = λ (⟨ Baa , ⟨ Bbb , Bcc ⟩ ⟩) → refl
    }

---------------------------------------------------
-- Existentials

-- Given a variable x of type A and a proposition B x which contains x as a free variable,
-- the existentially quantified proposition Σ[ x ∈ A ] B x holds if for some term M of type A the proposition B M holds.
-- Here B M stands for the proposition B x with each free occurrence of x replaced by M.
-- Variable x appears free in B x but bound in Σ[ x ∈ A ] B x.

-- We formalise existential quantification by declaring a suitable inductive type:

-- data Σ (A : Set) (B : A → Set) : Set where
--   ⟨_,_⟩ : (x : A) → B x → Σ A B

-- We define a convenient syntax for existentials as follows:

-- Σ-syntax = Σ
-- infix 2 Σ-syntax
-- syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

-- This is our first use of a syntax declaration, which specifies that the term on the left
-- may be written with the syntax on the right.
--
-- The special syntax is available only when the identifier Σ-syntax is imported.
--
-- Evidence that Σ[ x ∈ A ] B x holds is of the form ⟨ M , N ⟩ where M is a term of type A, and N is evidence that B M holds.

-- Equivalently, we could also declare existentials as a record type:
record Σ (A : Set) (B : A → Set) : Set where
  constructor ⟨_,_⟩
  field
    proj₁′ : A
    proj₂′ : B proj₁′
open Σ

Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

{- Example:

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field fst : A
        snd : B fst

syntax Σ A (λ x → B) = [ x ∈ A ] × B

witness : ∀ {A B} → [ x ∈ A ] × B → A
witness (x , _) = x
-}

-- Products arise as a special case of existentials,
-- where the second component does not depend on a variable drawn from the first component.

-- When a product is viewed as evidence of a conjunction, both of its components are viewed as evidence,
-- whereas when it is viewed as evidence of an existential, the first component is viewed as an element
-- of a datatype and the second component is viewed as evidence of a proposition that depends on the first component.
--
-- This difference is largely a matter of interpretation, since in Agda a value of a type and evidence
-- of a proposition are indistinguishable.

-- Existentials are sometimes referred to as dependent sums,
-- because if A is a finite type with values x₁ , ⋯ , xₙ,
-- and if each of the types B x₁ , ⋯ B xₙ has m₁ , ⋯ , mₙ distinct members,
-- then Σ[ x ∈ A ] B x has m₁ + ⋯ + mₙ members,
-- which explains the choice of notation for existentials, since Σ stands for sum.

-- Existentials are sometimes referred to as dependent products, since products arise as a special case.
-- However, that choice of names is doubly confusing,
-- since universals also have a claim to the name dependent product
-- and since existentials also have a claim to the name dependent sum.

-- A common notation for existentials is ∃ (analogous to ∀ for universals).
-- We follow the convention of the Agda standard library, and reserve this
-- notation for the case where the domain of the bound variable is left implicit:

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

-- The special syntax is available only when the identifier ∃-syntax is imported.
-- We will tend to use this syntax, since it is shorter and more familiar.

∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
  → ∃[ x ] B x
    ---------------
  → C
∃-elim f ⟨ x , y ⟩ = f x y
-- In other words, if we know for every x of type A that B x implies C, and we know for some x of type A that B x holds,
-- then we may conclude that C holds.

-- Indeed, the converse also holds, and the two together form an isomorphism:

∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying =
  record
    { to      =  λ{ f → λ{ ⟨ x , y ⟩ → f x y }}
    ; from    =  λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ }}}
    ; from∘to =  λ{ f → refl }
    ; to∘from =  λ{ g → extensionality λ{ ⟨ x , y ⟩ → refl }}
    }
-- The result can be viewed as a generalisation of currying.

----------------------------------------------
-- Exercises

-- Show that existentials distribute over disjunction:

∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-distrib-⊎ =
  record
    { to      = λ{ ⟨ x , inj₁ Bx ⟩ → inj₁ ⟨ x , Bx ⟩ ; ⟨ x , inj₂ Cx ⟩ → inj₂ ⟨ x , Cx ⟩ }
    ; from    = λ{ (inj₁ ⟨ x , Bx ⟩) → ⟨ x , inj₁ Bx ⟩ ; (inj₂ ⟨ x , Cx ⟩) → ⟨ x , inj₂ Cx ⟩ }
    ; from∘to = λ{ ⟨ x , inj₁ Bx ⟩ → refl ; ⟨ x , inj₂ Cx ⟩ → refl }
    ; to∘from = λ{ (inj₁ ⟨ x , Bx ⟩) → refl ; (inj₂ ⟨ x , Cx ⟩) → refl }
    }

-- Show that an existential of conjunctions implies a conjunction of existentials:

∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
∃×-implies-×∃ ⟨ x , ⟨ Bx , Cx ⟩ ⟩ = ⟨ ⟨ x , Bx ⟩ , ⟨ x , Cx ⟩ ⟩

-- Does the converse hold? If so, prove; if not, explain why.
-- You cannot guarantee that x₁ and x₂ in (∃[ x₁ ] B x₁) × (∃[ x₂ ] C x₂) are the same.

∃-⊎ : ∀ {B : Tri → Set} →
  (∃[ x ] B x) ≃ (B aa ⊎ B bb ⊎ B cc)
∃-⊎ =
  record
    { to      = λ{ ⟨ aa , Baa ⟩ → inj₁ Baa ; ⟨ bb , Bbb ⟩ → inj₂ (inj₁ Bbb) ; ⟨ cc , Bcc ⟩ → inj₂ (inj₂ Bcc) }
    ; from    = λ{ (inj₁ Baa) → ⟨ aa , Baa ⟩ ; (inj₂ (inj₁ Bbb)) → ⟨ bb , Bbb ⟩ ; (inj₂ (inj₂ Bcc)) → ⟨ cc , Bcc ⟩}
    ; from∘to = λ{ ⟨ aa , Baa ⟩ → refl ; ⟨ bb , Bbb ⟩ → refl ; ⟨ cc , Bcc ⟩ → refl }
    ; to∘from = λ{ (inj₁ Baa) → refl ; (inj₂ (inj₁ Bbb)) → refl ; (inj₂ (inj₂ Bcc)) → refl}
    }

-------------------------------------------------------
-- An existential example

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

-- This completes the proof in the forward direction.

even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (    m * 2 ≡ n)
odd-∃  : ∀ {n : ℕ} →  odd n → ∃[ m ] (1 + m * 2 ≡ n)

even-∃ even-zero                       =  ⟨ zero , refl ⟩
even-∃ (even-suc o) with odd-∃ o
...                    | ⟨ m , refl ⟩  =  ⟨ suc m , refl ⟩

odd-∃  (odd-suc e)  with even-∃ e
...                    | ⟨ m , refl ⟩  =  ⟨ m , refl ⟩

-- Here is the proof in the reverse direction:

∃-even : ∀ {n : ℕ} → ∃[ m ] (    m * 2 ≡ n) → even n
∃-odd  : ∀ {n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) →  odd n

∃-even ⟨  zero , refl ⟩  =  even-zero
∃-even ⟨ suc m , refl ⟩  =  even-suc (∃-odd ⟨ m , refl ⟩)

∃-odd  ⟨     m , refl ⟩  =  odd-suc (∃-even ⟨ m , refl ⟩)

-- Show that y ≤ z holds if and only if there exists a x such that x + y ≡ z.

open import plfa.part1.Equality using (sym ; cong; ≡-implies-≤; +-monoˡ-≤)
open import plfa.part1.Induction using (+-rearrange; +-comm; +-suc; +-identityʳ; +-assoc)
open _≤_

postulate
  ≤-suc : ∀ {x y z : ℕ}
    → x ≤ y
       -------------
    → x ≤ y + z

∃→≤ : ∀ {y z : ℕ}
  → ∃[ x ] (x + y ≡ z)
     ------------------
  → y ≤ z
∃→≤ ⟨ zero , y≡z ⟩ = ≡-implies-≤ y≡z
∃→≤ {y} {suc z'} ⟨ suc x , refl ⟩ = +-monoˡ-≤ 0 (suc x) y z≤n

≤→∃ : ∀ {y z : ℕ}
  → y ≤ z
     ------------------
  → ∃[ x ] (x + y ≡ z)
≤→∃ {zero} {z} z≤n = ⟨ z , +-identityʳ z ⟩
≤→∃ (s≤s y≤z) with ≤→∃ y≤z
... | ⟨ x , x+y≡z ⟩ = ⟨ x , suc-≡ʳ x+y≡z ⟩
  where
    suc-≡ʳ : ∀ {x y z : ℕ}
      → x + y ≡ z
        ------------------
      → x + suc y ≡ suc z
    suc-≡ʳ {zero} y≡z = cong suc y≡z
    suc-≡ʳ {suc x} {y} suc-xy≡z rewrite +-suc x y = cong suc suc-xy≡z

-------------------------------------------
-- Existentials, Universals, and Negation

-- Negation of an existential is isomorphic to the universal of a negation.
-- Considering that existentials are generalised disjunction and universals are generalised conjunction,
-- this result is analogous to the one which tells us that negation of a disjunction is
-- isomorphic to a conjunction of negations:

¬∃≃∀¬ : ∀ {A : Set} {B : A → Set}
  → (¬ ∃[ x ] B x) ≃ ∀ x → ¬ B x
¬∃≃∀¬ =
  record
    { to      =  λ{ ¬∃xy x y → ¬∃xy ⟨ x , y ⟩ }
    ; from    =  λ{ ∀¬xy ⟨ x , y ⟩ → ∀¬xy x y }
    ; from∘to =  λ{ ¬∃xy → extensionality λ{ ⟨ x , y ⟩ → refl } }
    ; to∘from =  λ{ ∀¬xy → refl }
    }

----------------------------------------------
-- Exercises

∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
  → ∃[ x ] (¬ B x)
    --------------
  → ¬ (∀ x → B x)
∃¬-implies-¬∀ ⟨ x , ¬Bx ⟩ ∀x→Bx = ¬Bx (∀x→Bx x)

-- Does the converse hold? If so, prove; if not, explain why.

-- In order to solve this problem you would need to pattern match on ⊥ but that is not possible.
--
-- ¬∀-implies-∃¬ : ∀ {A : Set} {B : A → Set}
--   → ¬ (∀ x → B x)
--     --------------
--   → ∃[ x ] (¬ B x)
-- ¬∀-implies-∃¬  ¬∀x→Bx = ⟨ {!!} , (λ{x → ¬∀x→Bx {!!} }) ⟩

open import plfa.part1.Relations using (Bin ; One ; Can ; to ; from ; inc-can ; to-can ; from-to-can)

postulate
  from∘to : ∀ (n : ℕ) → from (to n) ≡ n

open Bin
open One
open Can

≡One : ∀{b : Bin} (o o' : One b) → o ≡ o'
≡One one one = refl
≡One (suc₀ o) (suc₀ o') = cong suc₀ (≡One o o')
≡One (suc₁ o) (suc₁ o') = cong suc₁ (≡One o o')

≡Can : ∀{b : Bin} (cb : Can b) (cb' : Can b) → cb ≡ cb'
≡Can zero zero = refl
≡Can zero (leading-one (suc₀ ()))
≡Can (leading-one (suc₀ ())) zero
≡Can (leading-one x) (leading-one x₁) = cong leading-one (≡One x x₁)

-- Many of the alternatives for proving to∘from turn out to be tricky.
-- However, the proof can be straightforward if you use the following lemma, which is a corollary of ≡Can.

proj₁≡→Can≡ : {cb cb′ : ∃[ b ](Can b)} → proj₁′ cb ≡ proj₁′ cb′ → cb ≡ cb′
proj₁≡→Can≡ {⟨ proj₁′₁ , proj₂′₁ ⟩} {⟨ proj₁′₂ , proj₂′₂ ⟩} refl rewrite ≡Can proj₂′₁ proj₂′₂ = refl

ℕ≃Can : ℕ ≃ ∃[ b ](Can b)
ℕ≃Can =
  record
    { to      = λ{n → ⟨ to n , to-can n ⟩}
    ; from    = λ{⟨ b , _ ⟩ → from b}
    ; from∘to = from∘to
    ; to∘from = λ{⟨ b , canB ⟩ → proj₁≡→Can≡ (from-to-can canB) }
    }

-------------------------------------------------
-- Standard library

import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
