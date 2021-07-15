module plfa.part1.Decidable where

-- We have a choice as to how to represent relations:
-- * as an inductive data type of evidence that the relation holds,
-- * or as a function that computes whether the relation holds.
--
-- We first explore the familiar notion of booleans, but later discover
-- that these are best avoided in favour of a new notion of decidable.

---------------------------------------------------
-- Imports

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using ()
  renaming (contradiction to ¬¬-intro)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import plfa.part1.Relations using (_<_; z<s; s<s)
open import plfa.part1.Isomorphism using (_⇔_)

---------------------------------------------
-- Evidence vs Computation

data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ}
      --------
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}
    → m ≤ n
      -------------
    → suc m ≤ suc n
infix 4 _≤_

2≤4 : 2 ≤ 4
2≤4 = s≤s (s≤s z≤n)

¬4≤2 : ¬ (4 ≤ 2)
¬4≤2 (s≤s (s≤s ()))
-- The occurrence of () attests to the fact that there is no possible evidence for 2 ≤ 0,
-- which z≤n cannot match (because 2 is not zero) and s≤s cannot match (because 0 cannot match suc n).

data Bool : Set where
  true  : Bool
  false : Bool

-- Given booleans, we can define a function of two numbers that computes to true if the comparison holds
-- and to false otherwise:

_≤ᵇ_ : ℕ → ℕ → Bool
zero ≤ᵇ n       =  true
suc m ≤ᵇ zero   =  false
suc m ≤ᵇ suc n  =  m ≤ᵇ n
infix 4 _≤ᵇ_

_ : (2 ≤ᵇ 4) ≡ true
_ =
  begin
    2 ≤ᵇ 4
  ≡⟨⟩
    1 ≤ᵇ 3
  ≡⟨⟩
    0 ≤ᵇ 2
  ≡⟨⟩
    true
  ∎

_ : (4 ≤ᵇ 2) ≡ false
_ =
  begin
    4 ≤ᵇ 2
  ≡⟨⟩
    3 ≤ᵇ 1
  ≡⟨⟩
    2 ≤ᵇ 0
  ≡⟨⟩
    false
  ∎

-------------------------------------------
-- Relating evidence and computation

-- We would hope to be able to show these two approaches are related, and indeed we can.

-- First, we define a function that lets us map from the computation world to the evidence world:

T : Bool → Set
T true   =  ⊤
T false  =  ⊥

-- If b is of type Bool, then tt provides evidence that T b holds if b is true,
-- while there is no possible evidence that T b holds if b is false.

-- Another way to put this is that T b is inhabited exactly when b ≡ true is inhabited.
-- In the forward direction, we need to do a case analysis on the boolean b:

T→≡ : ∀ (b : Bool) → T b → b ≡ true
T→≡ true  tt = refl
T→≡ false ()

≡→T : ∀ {b : Bool} → b ≡ true → T b
≡→T refl  =  tt

-- If b ≡ true is inhabited by refl we know that b is true and hence T b is inhabited by tt.
--
-- Now we can show that T (m ≤ᵇ n) is inhabited exactly when m ≤ n is inhabited.

-- In the forward direction,
≤ᵇ→≤ : ∀ (m n : ℕ) → T (m ≤ᵇ n) → m ≤ n
≤ᵇ→≤ zero    n       tt  =  z≤n
≤ᵇ→≤ (suc m) zero    ()
≤ᵇ→≤ (suc m) (suc n) t   =  s≤s (≤ᵇ→≤ m n t)

-- In the reverse direction, we consider the possible forms of evidence that m ≤ n:
≤→≤ᵇ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ n)
≤→≤ᵇ z≤n        =  tt
≤→≤ᵇ (s≤s m≤n)  =  ≤→≤ᵇ m≤n
-- If the evidence is s≤s applied to m≤n, then suc m ≤ᵇ suc n reduces to m ≤ᵇ n,
-- and we may recursively invoke the function to produce evidence that T (m ≤ᵇ n).

-- The forward proof has one more clause than the reverse proof,
-- precisely because in the forward proof we need clauses corresponding
-- to the comparison yielding both true and false, while in the reverse proof
-- we only need clauses corresponding to the case where there is evidence
-- that the comparison holds. This is exactly why we tend to prefer the
-- evidence formulation to the computation formulation, because it allows us to do less work:
-- we consider only cases where the relation holds, and can ignore those where it does not.

-- On the other hand, sometimes the computation formulation may be just what we want.
-- Given a non-obvious relation over large values, it might be handy to have the computer work out the answer for us.
-- Fortunately, rather than choosing between evidence and computation, there is a way to get the benefits of both.

--------------------------------------
-- The best of both worlds

-- A function that returns a boolean returns exactly a single bit of information:
-- does the relation hold or does it not? Conversely, the evidence approach tells us
-- exactly why the relation holds, but we are responsible for generating the evidence.
--
-- But it is easy to define a type that combines the benefits of both approaches.
--
-- It is called Dec A, where Dec is short for decidable:

data Dec (A : Set) : Set where
  yes :   A → Dec A
  no  : ¬ A → Dec A

-- Like booleans, the type has two constructors. A value of type Dec A is either of the form yes x,
-- where x provides evidence that A holds, or of the form no ¬x, where ¬x provides evidence that A
-- cannot hold (that is, ¬x is a function which given evidence of A yields a contradiction).

-- For example, we define a function _≤?_ which given two numbers decides whether one is less than or equal to the other,
-- and provides evidence to justify its conclusion.

-- First, we introduce two functions useful for constructing evidence that an inequality does not hold:

¬s≤z : ∀ {m : ℕ} → ¬ (suc m ≤ zero)
¬s≤z ()

¬s≤s : ∀ {m n : ℕ} → ¬ (m ≤ n) → ¬ (suc m ≤ suc n)
¬s≤s ¬m≤n (s≤s m≤n) = ¬m≤n m≤n

-- (A subtlety: if we do not define ¬s≤z and ¬s≤s as top-level functions,
-- but instead use inline anonymous functions then Agda may have trouble normalising evidence of negation.)

--  Using these, it is straightforward to decide an inequality:

_≤?_ : ∀ (m n : ℕ) → Dec (m ≤ n)
zero  ≤? n                   =  yes z≤n
suc m ≤? zero                =  no ¬s≤z
suc m ≤? suc n with m ≤? n
...               | yes m≤n  =  yes (s≤s m≤n)
...               | no ¬m≤n  =  no (¬s≤s ¬m≤n)

-- When we wrote _≤ᵇ_, we had to write two other functions, ≤ᵇ→≤ and ≤→≤ᵇ, in order to show that it was correct.
-- In contrast, the definition of _≤?_ proves itself correct, as attested to by its type.
-- The code of _≤?_ is far more compact than the combined code of _≤ᵇ_, ≤ᵇ→≤, and ≤→≤ᵇ.
-- As we will later show, if you really want the latter three, it is easy to derive them from _≤?_.


--  We can use our new function to compute the evidence that earlier we had to think up on our own:
_ : 2 ≤? 4 ≡ yes (s≤s (s≤s z≤n))
_ = refl

_ : 4 ≤? 2 ≡ no (¬s≤s (¬s≤s ¬s≤z))
_ = refl

-- You can check that Agda will indeed compute these values.
-- Typing C-c C-n and providing 2 ≤? 4 or 4 ≤? 2 as the requested expression causes Agda to print the values given above.

-------------------
-- Exercises


¬z<z : ¬ (zero < zero)
¬z<z ()

¬s<z : ∀ {m : ℕ} → ¬ (suc m < zero)
¬s<z ()

¬s<s : ∀ {m n : ℕ} → ¬ (m < n) → ¬ (suc m < suc n)
¬s<s ¬m<n (s<s m<n) = ¬m<n m<n

_<?_ : ∀ (m n : ℕ) → Dec (m < n)
zero <? zero = no ¬z<z
zero <? suc n = yes z<s
suc m <? zero = no ¬s<z
suc m <? suc n with m <? n
... | yes  m<n = yes (s<s m<n)
... |  no ¬m<n = no (¬s<s ¬m<n)

¬z≡s : ∀ {n : ℕ} → ¬ (zero ≡ suc n)
¬z≡s ()

¬s≡z : ∀ {n : ℕ} → ¬ (suc n ≡ zero)
¬s≡z ()

open import Data.Nat.Properties using (suc-injective)

¬s≡s : ∀ {m n : ℕ} → ¬ (m ≡ n) → ¬ (suc m ≡ suc n)
¬s≡s ¬m≡n s≡s = ¬m≡n (suc-injective s≡s)

_≡ℕ?_ : ∀ (m n : ℕ) → Dec (m ≡ n)
zero ≡ℕ? zero = yes refl
zero ≡ℕ? suc n = no ¬z≡s
suc m ≡ℕ? zero = no ¬s≡z
suc m ≡ℕ? suc n with m ≡ℕ? n
... | yes m≡n = yes (Eq.cong suc m≡n)
... | no ¬m≡n = no (¬s≡s ¬m≡n)

-------------------------------------------------------------
-- Decidables from booleans, and booleans from decidables
