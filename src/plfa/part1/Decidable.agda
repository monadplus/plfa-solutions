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

open import Data.Nat.Properties using (suc-injective)

¬z≡s : ∀ {n : ℕ} → ¬ (zero ≡ suc n)
¬z≡s ()

¬s≡z : ∀ {n : ℕ} → ¬ (suc n ≡ zero)
¬s≡z ()

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

-- Curious readers might wonder if we could reuse the definition of m ≤ᵇ n,
-- together with the proofs that it is equivalent to m ≤ n, to show decidability.
--
-- Indeed, we can do so as follows:

_≤?′_ : ∀ (m n : ℕ) → Dec (m ≤ n)
m ≤?′ n with m ≤ᵇ n | ≤ᵇ→≤ m n | ≤→≤ᵇ {m} {n}
...        | true   | p         | _            = yes (p tt)
...        | false  | _         | ¬p           = no ¬p

{-
The triple binding of the with clause in this proof is essential. If instead we wrote:

  _≤?″_ : ∀ (m n : ℕ) → Dec (m ≤ n)
  m ≤?″ n with m ≤ᵇ n
  ... | true   =  yes (≤ᵇ→≤ m n tt)
  ... | false  =  no (≤→≤ᵇ {m} {n})

then Agda would make two complaints, one for each clause:

  ⊤ !=< (T (m ≤ᵇ n)) of type Set
  when checking that the expression tt has type T (m ≤ᵇ n)

  T (m ≤ᵇ n) !=< ⊥ of type Set
  when checking that the expression ≤→≤ᵇ {m} {n} has type ¬ m ≤ n

Putting the expressions into the with clause permits Agda to exploit the fact
that T (m ≤ᵇ n) is ⊤ when m ≤ᵇ n is true, and that T (m ≤ᵇ n) is ⊥ when m ≤ᵇ n is false.

However, overall it is simpler to just define _≤?_ directly, as in the previous section.
If one really wants _≤ᵇ_, then it and its properties are easily derived from _≤?_, as we will now show.
-}

-- Erasure takes a decidable value to a boolean:
⌊_⌋ : ∀ {A : Set} → Dec A → Bool
⌊ yes x ⌋  =  true
⌊ no ¬x ⌋  =  false

-- Using erasure, we can easily derive _≤ᵇ_ from _≤?_:
_≤ᵇ′_ : ℕ → ℕ → Bool
m ≤ᵇ′ n  =  ⌊ m ≤? n ⌋

-- Further, *if D is a value of type Dec A, then T ⌊ D ⌋ is inhabited exactly when A is inhabited*:
toWitness : ∀ {A : Set} {D : Dec A} → T ⌊ D ⌋ → A
toWitness {A} {yes x} tt  =  x
toWitness {A} {no ¬x} ()

fromWitness : ∀ {A : Set} {D : Dec A} → A → T ⌊ D ⌋
fromWitness {A} {yes x} _  =  tt
fromWitness {A} {no ¬x} x  =  ¬x x

-- Using these, we can easily derive that T (m ≤ᵇ′ n) is inhabited exactly when m ≤ n is inhabited:
≤ᵇ′→≤ : ∀ {m n : ℕ} → T (m ≤ᵇ′ n) → m ≤ n
≤ᵇ′→≤ = toWitness

≤→≤ᵇ′ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ′ n)
≤→≤ᵇ′  =  fromWitness

--- In summary, it is usually best to eschew booleans and rely on decidables.
--- If you need booleans, they and their properties are easily derived from the corresponding decidables.

--------------------------------------
-- Logical connectives

infixr 6 _∧_

_∧_ : Bool → Bool → Bool
true  ∧ true  = true
false ∧ _     = false
_     ∧ false = false

-- In Emacs, the left-hand side of the third equation displays in grey,
-- indicating that the order of the equations determines which of the second or the third can match.
-- However, regardless of which matches the answer is the same.

-- Correspondingly, given two decidable propositions, we can decide their conjunction:
_×-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A × B)
yes x ×-dec yes y = yes ⟨ x , y ⟩
no ¬x ×-dec _     = no λ{ ⟨ x , y ⟩ → ¬x x }
_     ×-dec no ¬y = no λ{ ⟨ x , y ⟩ → ¬y y }

-- The disjunction of two booleans is true if either is true, and false if both are false:
infixr 5 _∨_

_∨_ : Bool → Bool → Bool
true  ∨ _      = true
_     ∨ true   = true
false ∨ false  = false

-- Correspondingly, given two decidable propositions, we can decide their disjunction:
infixr 5 _⊎-dec_

_⊎-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⊎ B)
yes x ⊎-dec _     = yes (inj₁ x)
_     ⊎-dec yes y = yes (inj₂ y)
no ¬x ⊎-dec no ¬y = no λ{ (inj₁ x) → ¬x x ; (inj₂ y) → ¬y y }

-- The negation of a boolean is false if its argument is true, and vice versa:
not : Bool → Bool
not true  = false
not false = true

-- Correspondingly, given a decidable proposition, we can decide its negation:
¬? : ∀ {A : Set} → Dec A → Dec (¬ A)
¬? (yes x)  =  no (¬¬-intro x)
¬? (no ¬x)  =  yes ¬x

-- There is also a slightly less familiar connective, corresponding to implication:

_⊃_ : Bool → Bool → Bool
_     ⊃ true   =  true
false ⊃ _      =  true
true  ⊃ false  =  false

-- Correspondingly, given two decidable propositions, we can decide if the first implies the second:
_→-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A → B)
_     →-dec yes y  =  yes (λ _ → y)
no ¬x →-dec _      =  yes (λ x → ⊥-elim (¬x x))
yes x →-dec no ¬y  =  no (λ f → ¬y (f x))

------------------------------------------
-- Exercises

∧-× : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∧ ⌊ y ⌋ ≡ ⌊ x ×-dec y ⌋
∧-× (yes x) (yes y) = refl
∧-× (yes x) (no y) = refl
∧-× (no x) y = refl

∨-⊎ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∨ ⌊ y ⌋ ≡ ⌊ x ⊎-dec y ⌋
∨-⊎ (yes x) y = refl
∨-⊎ (no x) (yes x₁) = refl
∨-⊎ (no x) (no x₁) = refl

not-¬ : ∀ {A : Set} (x : Dec A) → not ⌊ x ⌋ ≡ ⌊ ¬? x ⌋
not-¬ (yes x) = refl
not-¬ (no x) = refl

_iff_ : Bool → Bool → Bool
true  iff true = true
false iff true = false
true  iff false = false
false iff false = true

-- _iff_ : Bool → Bool → Bool
-- true  iff b = b
-- false iff b = not b

open _⇔_

_⇔-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⇔ B)
yes a ⇔-dec yes b = yes record { to = λ _ → b ; from = λ _ → a}
yes a ⇔-dec no ¬b = no (λ{ A⇔B → ¬b (to A⇔B a)})
no ¬a ⇔-dec yes b = no (λ{ A⇔B → ¬a (from A⇔B b)})
no ¬a ⇔-dec no ¬b = yes record { to = λ a → ⊥-elim (¬a a) ; from = λ b → ⊥-elim (¬b b) }

iff-⇔ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ iff ⌊ y ⌋ ≡ ⌊ x ⇔-dec y ⌋
iff-⇔ (yes x) (yes x₁) = refl
iff-⇔ (yes x) (no x₁) = refl
iff-⇔ (no x) (yes x₁) = refl
iff-⇔ (no x) (no x₁) = refl

-----------------------------
-- Proof by reflection

-- Let’s revisit our definition of monus from Chapter Naturals.
-- If we subtract a larger number from a smaller number, we take the result to be zero.
-- We had to do something, after all. What could we have done differently?
-- We could have defined a guarded version of minus, a function which subtracts n from m only if n ≤ m:

minus : (m n : ℕ) (n≤m : n ≤ m) → ℕ
minus m       zero    _         = m
minus (suc m) (suc n) (s≤s n≤m) = minus m n n≤m

-- Unfortunately, it is painful to use, since we have to explicitly provide the proof that n ≤ m:

_ : minus 5 3 (s≤s (s≤s (s≤s z≤n))) ≡ 2
_ = refl

-- We cannot solve this problem in general, but in the scenario above, we happen to know the two numbers statically.
-- In that case, we can use a technique called proof by reflection.
-- Essentially, we can ask Agda to run the decidable equality n ≤? m while type checking, and make sure that n ≤ m!

-- We do this by using a feature of implicits. Agda will fill in an implicit of a record type
-- if it can fill in all its fields. So Agda will always manage to fill in an implicit of an empty record type,
-- since there aren’t any fields after all. This is why ⊤ is defined as an empty record.

-- The trick is to have an implicit argument of the type T ⌊ n ≤? m ⌋.
-- Let’s go through what this means step-by-step. First, we run the decision procedure, n ≤? m.
-- This provides us with evidence whether n ≤ m holds or not.
-- We erase the evidence to a boolean. Finally, we apply T.
-- Recall that T maps booleans into the world of evidence: true becomes the unit type ⊤,
-- and false becomes the empty type ⊥. Operationally, an implicit argument of this type works as a guard.

--  If n ≤ m holds, the type of the implicit value reduces to ⊤. Agda then happily provides the implicit value.
--  Otherwise, the type reduces to ⊥, which Agda has no chance of providing, so it will throw an error.
--  For instance, if we call 3 - 5 we get _n≤m_254 : ⊥.

-- We obtain the witness for n ≤ m using toWitness, which we defined earlier:
_-_ : (m n : ℕ) {n≤m : T ⌊ n ≤? m ⌋} → ℕ
_-_ m n {n≤m} = minus m n (toWitness n≤m)

-- We can safely use _-_ as long as we statically know the two numbers:
_ : 5 - 3 ≡ 2
_ = refl

-- It turns out that this idiom is very common. The standard library defines a synonym for T ⌊ ? ⌋ called True:
True : ∀ {Q} → Dec Q → Set
True Q = T ⌊ Q ⌋

-- _-′_ : (m n : ℕ) {n≤m : True (n ≤? m)} → ℕ
-- _-′_ m n {n≤m} = minus m n (toWitness n≤m)

----------------------
-- Exercise

toWitnessFalse : ∀ {A : Set} {D : Dec (¬ A)} → T ⌊ D ⌋ → ¬ A
toWitnessFalse {A} {yes ¬A} tt = ¬A
toWitnessFalse {_} {no _} ()

fromWitnessFalse : ∀ {A : Set} {D : Dec (¬ A)} → ¬ A → T ⌊ D ⌋
fromWitnessFalse {A} {yes ¬A} _ = tt
fromWitnessFalse {A} {no ¬¬A} ¬A = ¬¬A ¬A

False : ∀ {Q} → Dec (¬ Q) → Set
False Q = T (not ⌊ Q ⌋)

-----------------------------------------------------
-- Standard Library

import Data.Bool.Base using (Bool; true; false; T; _∧_; _∨_; not)
import Data.Nat using (_≤?_)
import Relation.Nullary using (Dec; yes; no)
import Relation.Nullary.Decidable using (⌊_⌋; True; toWitness; fromWitness)
import Relation.Nullary.Negation using (¬?)
import Relation.Nullary.Product using (_×-dec_)
import Relation.Nullary.Sum using (_⊎-dec_)
import Relation.Binary using (Decidable)
