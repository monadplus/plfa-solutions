module plfa.part1.Decidable where

-- We have a choice as to how to represent relations:
--   as an inductive data type of evidence that the relation holds,
--   or as a function that computes whether the relation holds.
-- Here we explore the relation between these choices.
-- We first explore the familiar notion of booleans, but later discover
-- that these are best avoided in favour of a new notion of decidable.

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
