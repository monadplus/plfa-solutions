module plfa.part2.Lambda where

-- This chapter formalises the simply-typed lambda calculus, giving its syntax, small-step semantics, and typing rules.
-- The next chapter Properties proves its main properties, including progress and preservation.
-- Following chapters will look at a number of variants of lambda calculus.

-- Be aware that the approach we take here is not our recommended approach to formalisation.
-- Using de Bruijn indices and intrinsically-typed terms, as we will do in Chapter DeBruijn, leads to a more compact formulation.
-- Nonetheless, we begin with named variables and extrinsically-typed terms, partly because names are easier
-- than indices to read, and partly because the development is more traditional.

-- The development in this chapter was inspired by the corresponding development in Chapter Stlc of Software Foundations
-- (Programming Language Foundations). We differ by representing contexts explicitly (as lists pairing identifiers with types)
-- rather than as partial maps (which take identifiers to types), which corresponds better to
-- our subsequent development of DeBruijn notation. We also differ by taking natural numbers as the base type
-- rather than booleans, allowing more sophisticated examples. In particular, we will be able to show (twice!)
-- that two plus two is four.

-----------------------------------------------
-- Imports

open import Data.Bool using (T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _×_)
open import Data.String using (String; _≟_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋; False; toWitnessFalse)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

-----------------------------------------------
-- Syntax of terms

{-

Terms have seven constructs. Three are for the core lambda calculus:

    Variables ` x
    Abstractions ƛ x ⇒ N
    Applications L · M

Three are for the naturals:

    Zero `zero
    Successor `suc M
    Case case L [zero⇒ M |suc x ⇒ N ]

And one is for recursion:

    Fixpoint μ x ⇒ M

Abstraction is also called lambda abstraction, and is the construct from which the calculus takes its name.

With the exception of variables and fixpoints, each term form either constructs a value of
a given type (abstractions yield functions, zero and successor yield natural numbers)
or deconstructs it (applications use functions, case terms use naturals).
We will see this again when we come to the rules for assigning types to terms,
where constructors correspond to introduction rules and deconstructors to eliminators.

Here is the syntax of terms in Backus-Naur Form (BNF):

L, M, N  ::=
  ` x  |  ƛ x ⇒ N  |  L · M  |
  `zero  |  `suc M  |  case L [zero⇒ M |suc x ⇒ N ]  |
  μ x ⇒ M


-}

--  And here it is formalised in Agda:

Id : Set
Id = String

infix  5  ƛ_⇒_   -- Gl-
infix  5  μ_⇒_   -- mu
infixl 7  _·_     -- cdot
infix  8  `suc_
infix  9  `_

data Term : Set where
  `_                      :  Id → Term
  ƛ_⇒_                   :  Id → Term → Term
  _·_                     :  Term → Term → Term
  `zero                   :  Term
  `suc_                   :  Term → Term
  case_[zero⇒_|suc_⇒_]  :  Term → Term → Id → Term → Term
  μ_⇒_                   :  Id → Term → Term

-- We choose precedence so that lambda abstraction and fixpoint bind least tightly, then application,
-- then successor, and tightest of all is the constructor for variables. Case expressions are self-bracketing.

------------------------------
-- Example terms

two : Term
two = `suc `suc `zero

plus : Term
plus = μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
         case ` "m"
           [zero⇒ ` "n"
           |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]

-- Any use of “m” in the successor branch must refer to the latter binding,
-- and so we say that the latter binding **shadows** the former.

-- Later we will confirm that two plus two is four, in other words that the term
--
--    plus · two · two
--
-- reduces to `suc `suc `suc `suc `zero.

-- As a second example, we use higher-order functions to represent natural numbers.
-- In particular, the number n is represented by a function that accepts two arguments
-- and applies the first n times to the second. This is called the **Church representation** of the naturals.
--
-- Here are some example terms:
--   the Church numeral two
--   a function that adds Church numerals
--   a function to compute successor

twoᶜ : Term
twoᶜ =  ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")

plusᶜ : Term
plusᶜ =  ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
         ` "m" · ` "s" · (` "n" · ` "s" · ` "z")

sucᶜ : Term
sucᶜ = ƛ "n" ⇒ `suc (` "n")

-- To convert a Church numeral to the corresponding natural,
-- we apply it to the sucᶜ function and the natural number zero.

-- Again, later we will confirm that two plus two is four, in other words that the term
--
--   plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero
--
-- reduces to `suc `suc `suc `suc `zero.

---------------------------------
-- Exercises

-- mul
