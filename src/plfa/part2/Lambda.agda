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

mul : Term
mul = μ "*" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
        case ` "m"
          [zero⇒ `zero
          |suc "m" ⇒ plus · ` "n" · (` "*" · ` "m" · ` "n") ]

mulᶜ : Term
mulᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
        ` "m" · (ƛ "x" ⇒ ` "n" · ` "s" · ` "x") · ` "z"

mulᶜ′ : Term
mulᶜ′ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
       ` "m" · (ƛ "acc" ⇒ plusᶜ · ` "n" · ` "acc" · ` "s" · ` "z" ) · ` "z"

-- Some people find it annoying to write ` "x" instead of x.
-- We can make examples with lambda terms slightly easier to write by adding the following definitions:

ƛ′_⇒_ : Term → Term → Term
ƛ′ (` x) ⇒ N  =  ƛ x ⇒ N
ƛ′ _ ⇒ _      =  ⊥-elim impossible
  where postulate impossible : ⊥

case′_[zero⇒_|suc_⇒_] : Term → Term → Term → Term → Term
case′ L [zero⇒ M |suc (` x) ⇒ N ]  =  case L [zero⇒ M |suc x ⇒ N ]
case′ _ [zero⇒ _ |suc _ ⇒ _ ]      =  ⊥-elim impossible
  where postulate impossible : ⊥

μ′_⇒_ : Term → Term → Term
μ′ (` x) ⇒ N  =  μ x ⇒ N
μ′ _ ⇒ _      =  ⊥-elim impossible
  where postulate impossible : ⊥

-- If we use C-c C-n to normalise the term
--   ƛ′ two ⇒ two
-- Agda will return an answer warning us that the impossible has occurred:
--   ⊥-elim (plfa.part2.Lambda.impossible (`suc (`suc `zero)) (`suc (`suc `zero)))

-- While postulating the impossible is a useful technique, it must be used with care,
-- since such postulation could allow us to provide evidence of any proposition whatsoever, regardless of its truth.

plus′ : Term
plus′ = μ′ + ⇒ ƛ′ m ⇒ ƛ′ n ⇒
          case′ m
            [zero⇒ n
            |suc m ⇒ `suc (+ · m · n) ]
  where
  +  =  ` "+"
  m  =  ` "m"
  n  =  ` "n"


mul′ : Term
mul′ = μ′ * ⇒ ƛ′ m ⇒ ƛ′ n ⇒
        case′ n
          [zero⇒ `zero
          |suc m ⇒ plus′ · n · (* · m · n)]
  where
  * = ` "*"
  m = ` "m"
  n = ` "n"

----------------------------------
-- Formal vs informal

{-
In informal presentation of formal semantics, one uses choice of variable name to disambiguate
and writes x rather than ` x for a term that is a variable. Agda requires we distinguish.

Similarly, informal presentation often use the same notation for function types, lambda abstraction,
and function application in both the object language (the language one is describing) and
the meta-language (the language in which the description is written), trusting readers can use
context to distinguish the two. Agda is not quite so forgiving, so here we use ƛ x ⇒ N and L · M for the object language,
as compared to λ x → N and L M in our meta-language, Agda.
-}

--------------------------------------
-- Bound and free variables

{-
In an abstraction ƛ x ⇒ N we call x the bound variable and N the body of the abstraction.
A central feature of lambda calculus is that consistent renaming of bound variables leaves
the meaning of a term unchanged. Thus the five terms

    ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")
    ƛ "f" ⇒ ƛ "x" ⇒ ` "f" · (` "f" · ` "x")
    ƛ "sam" ⇒ ƛ "zelda" ⇒ ` "sam" · (` "sam" · ` "zelda")
    ƛ "z" ⇒ ƛ "s" ⇒ ` "z" · (` "z" · ` "s")
    ƛ "😇" ⇒ ƛ "😈" ⇒ ` "😇" · (` "😇" · ` "😈" )

are all considered equivalent. This equivalence relation is called **alpha renaming** (introduced by Haskell Curry).

As we descend from a term into its subterms, variables that are bound may become free. Consider the following terms:

    ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z") has both s and z as bound variables.
             ƛ "z" ⇒ ` "s" · (` "s" · ` "z") has z bound and s free.
                      ` "s" · (` "s" · ` "z") has both s and z as free variables.

We say that a term with no free variables is **closed**; otherwise it is **open**.
Of the three terms above, the first is closed and the other two are open.
We will focus on reduction of closed terms.

Different occurrences of a variable may be bound and free. In the term

(ƛ "x" ⇒ ` "x") · ` "x"

the inner occurrence of x is bound while the outer occurrence is free. By alpha renaming, the term above is equivalent to

(ƛ "y" ⇒ ` "y") · ` "x"

in which y is bound and x is free. A common convention, called the **Barendregt convention**,
is to use alpha renaming to ensure that the bound variables in a term are distinct from the free variables,
which can avoid confusions that may arise if bound and free variables have the same names.

Case and recursion also introduce bound variables, which are also subject to alpha renaming. In the term

μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
  case ` "m"
    [zero⇒ ` "n"
    |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]

notice that there are two binding occurrences of m, one in the first line and one in the last line. It is equivalent to the following term,

μ "plus" ⇒ ƛ "x" ⇒ ƛ "y" ⇒
  case ` "x"
    [zero⇒ ` "y"
    |suc "x′" ⇒ `suc (` "plus" · ` "x′" · ` "y") ]

where the two binding occurrences corresponding to m now have distinct names, x and x′.
-}

------------------------------------
-- Values

-- A value is a term that corresponds to an answer.
-- Thus, `suc `suc `suc `suc `zero is a value, while plus · two · two is not.
-- Following convention, we treat all function abstractions as values; thus, plus by itself is considered a value.

-- The predicate Value M holds if term M is a value:

data Value : Term → Set where

  V-ƛ : ∀ {x N}
      ---------------
    → Value (ƛ x ⇒ N)

  V-zero :
      -----------
      Value `zero

  V-suc : ∀ {V}
    → Value V
      --------------
    → Value (`suc V)

-- In what follows, we let V and W range over values.

-------------------------------
-- Formal vs Informal

-- In informal presentations of formal semantics, using V as the name of a metavariable
-- is sufficient to indicate that it is a value.
--
-- In Agda, we must explicitly invoke the Value predicate.

--------------------------------
-- Other approaches

-- An alternative is not to focus on closed terms, to treat variables as values,
-- and to treat ƛ x ⇒ N as a value only if N is a value.
--
-- Indeed, this is how Agda normalises terms.
-- We consider this approach in Chapter Untyped.

---------------------------------
-- Substitution

{-
The heart of lambda calculus is the operation of substituting one term for a variable in another term.
Substitution plays a key role in defining the operational semantics of function application.

  (ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) · sucᶜ · `zero
  (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero
  sucᶜ · (sucᶜ · `zero)

We write substitution as N [ x := V ], meaning “substitute term V for free occurrences of variable x in term N”.
Substitution works if V is any closed term; it need not be a value, but we use V since in fact we usually substitute values.

Here are some examples:

    (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) [ "s" := sucᶜ ] yields ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z").
    (sucᶜ · (sucᶜ · ` "z")) [ "z" := `zero ] yields sucᶜ · (sucᶜ · `zero).
    (ƛ "x" ⇒ ` "y") [ "y" := `zero ] yields ƛ "x" ⇒ `zero.
    (ƛ "x" ⇒ ` "x") [ "x" := `zero ] yields ƛ "x" ⇒ ` "x".
    (ƛ "y" ⇒ ` "y") [ "x" := `zero ] yields ƛ "y" ⇒ ` "y".

In the last but one example, substituting `zero for x in ƛ "x" ⇒ ` "x" does not yield ƛ "x" ⇒ `zero,
since x is bound in the lambda abstraction. The choice of bound names is irrelevant: both ƛ "x" ⇒ ` "x"
and ƛ "y" ⇒ ` "y" stand for the identity function. One way to think of this is that x within the body
of the abstraction stands for a different variable than x outside the abstraction, they just happen to have the same name.

We will give a definition of substitution that is only valid when term substituted for the variable is closed.
This is because substitution by terms that are not closed may require renaming of bound variables. For example:

    (ƛ "x" ⇒ ` "x" · ` "y") [ "y" := ` "x" · `zero] should not yield
    (ƛ "x" ⇒ ` "x" · (` "x" · `zero)).

Instead, we should rename the bound variable to avoid capture:

    (ƛ "x" ⇒ ` "x" · ` "y") [ "y" := ` "x" · `zero ] should yield
    ƛ "x′" ⇒ ` "x′" · (` "x" · `zero).

Here x′ is a fresh variable distinct from x.

Formal definition of substitution with suitable renaming is considerably more complex,
so we avoid it by restricting to substitution by closed terms, which will be adequate for our purposes.
-}

-- Here is the formal definition of substitution by closed terms in Agda:

infix 9 _[_:=_]

_[_:=_] : Term → Id → Term → Term
(` x) [ y := V ] with x ≟ y
... | yes _          =  V
... | no  _          =  ` x
(ƛ x ⇒ N) [ y := V ] with x ≟ y
... | yes _          =  ƛ x ⇒ N
... | no  _          =  ƛ x ⇒ N [ y := V ]
(L · M) [ y := V ]   =  L [ y := V ] · M [ y := V ]
(`zero) [ y := V ]   =  `zero
(`suc M) [ y := V ]  =  `suc M [ y := V ]
(case L [zero⇒ M |suc x ⇒ N ]) [ y := V ] with x ≟ y
... | yes _          =  case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N ]
... | no  _          =  case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N [ y := V ] ]
(μ x ⇒ N) [ y := V ] with x ≟ y
... | yes _          =  μ x ⇒ N
... | no  _          =  μ x ⇒ N [ y := V ]

-- Examples

_ : (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) [ "s" := sucᶜ ] ≡ ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")
_ = refl

_ : (sucᶜ · (sucᶜ · ` "z")) [ "z" := `zero ] ≡ sucᶜ · (sucᶜ · `zero)
_ = refl

_ : (ƛ "x" ⇒ ` "y") [ "y" := `zero ] ≡ ƛ "x" ⇒ `zero
_ = refl

_ : (ƛ "x" ⇒ ` "x") [ "x" := `zero ] ≡ ƛ "x" ⇒ ` "x"
_ = refl

_ : (ƛ "y" ⇒ ` "y") [ "x" := `zero ] ≡ ƛ "y" ⇒ ` "y"
_ = refl

_ : (ƛ "y" ⇒ ` "x" · (ƛ "x" ⇒ ` "x")) [ "x" := `zero ] ≡ ƛ "y" ⇒ `zero · (ƛ "x" ⇒ ` "x")
_ = refl

-- Exercise

infix 9 _[_:=_]′

_[_:=_]′ : Term → Id → Term → Term
_[ƛ_⇒_:=_]′ : Term → Id → Id → Term → Term

N [ƛ x ⇒ y := V ]′ with x ≟ y
... | yes _           = V
... | no _            = N [ y := V ]′

(` x) [ y := V ]′ with x ≟ y
... | yes _          =  V
... | no  _          =  ` x
(ƛ x ⇒ N) [ y := V ]′ = ƛ x ⇒ N [ƛ x ⇒ y := V ]′
(L · M) [ y := V ]′   =  L [ y := V ]′ · M [ y := V ]′
(`zero) [ y := V ]′   =  `zero
(`suc M) [ y := V ]′  =  `suc M [ y := V ]′
(case L [zero⇒ M |suc x ⇒ N ]) [ y := V ]′ =
  case L [ y := V ]′ [zero⇒ M [ y := V ]′ |suc x ⇒ N [ƛ x ⇒ y := V ]′ ]
(μ x ⇒ N) [ y := V ]′ = μ x ⇒ N [ƛ x ⇒ y := V ]′

------------------------------
-- Reduction

{-
We give the reduction rules for call-by-value lambda calculus. To reduce an application,
first we reduce the left-hand side until it becomes a value (which must be an abstraction);
then we reduce the right-hand side until it becomes a value; and finally we substitute the argument
for the variable in the abstraction.

In an informal presentation of the operational semantics, the rules for reduction of applications are written as follows:

L —→ L′
--------------- ξ-·₁
L · M —→ L′ · M

M —→ M′
--------------- ξ-·₂
V · M —→ V · M′

----------------------------- β-ƛ
(ƛ x ⇒ N) · V —→ N [ x := V ]

The rules break into two sorts. Compatibility rules direct us to reduce some part of a term.
We give them names starting with the Greek letter ξ (xi). Once a term is sufficiently reduced,
it will consist of a constructor and a deconstructor, in our case ƛ and ·, which reduces directly.
We give them names starting with the Greek letter β (beta) and such rules are traditionally called beta rules.

A bit of terminology: A term that matches the left-hand side of a reduction rule is called a *redex*.
In the redex (ƛ x ⇒ N) · V, we may refer to x as the *formal parameter* of the function,
and V as the *actual parameter* of the function application.
Beta reduction replaces the formal parameter by the actual parameter.

If a term is a value, then no reduction applies; conversely,
if a reduction applies to a term then it is not a value.
We will show in the next chapter that this exhausts the possibilities:
every well-typed term either reduces or is a value.


- For numbers, zero does not reduce and successor reduces the subterm.
- A case expression reduces its argument to a number, and then chooses the zero
  or successor branch as appropriate.
- A fixpoint replaces the bound variable by the entire fixpoint term;
  this is the one case where we substitute by a term that is not a value.
-}

-- Here are the rules formalised in Agda:

infix 4 _—→_

data _—→_ : Term → Term → Set where

  ξ-·₁ : ∀ {L L′ M}
    → L —→ L′
      -----------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {V M M′}
    → Value V
    → M —→ M′
      -----------------
    → V · M —→ V · M′

  β-ƛ : ∀ {x N V}
    → Value V
      ------------------------------
    → (ƛ x ⇒ N) · V —→ N [ x := V ]

  ξ-suc : ∀ {M M′}
    → M —→ M′
      ------------------
    → `suc M —→ `suc M′

  ξ-case : ∀ {x L L′ M N}
    → L —→ L′
      -----------------------------------------------------------------
    → case L [zero⇒ M |suc x ⇒ N ] —→ case L′ [zero⇒ M |suc x ⇒ N ]

  β-zero : ∀ {x M N}
      ----------------------------------------
    → case `zero [zero⇒ M |suc x ⇒ N ] —→ M

  β-suc : ∀ {x V M N}
    → Value V
      ---------------------------------------------------
    → case `suc V [zero⇒ M |suc x ⇒ N ] —→ N [ x := V ]

  β-μ : ∀ {x M}
      ------------------------------
    → μ x ⇒ M —→ M [ x := μ x ⇒ M ]

-- The reduction rules are carefully designed to ensure that subterms of a term are reduced to
-- values before the whole term is reduced. This is referred to as *call-by-value reduction*.
--
-- Further, we have arranged that subterms are reduced in a left-to-right order.
-- This means that reduction is *deterministic*: for any term, there is at most one other term to which it reduces.
-- Put another way, our reduction relation —→ is in fact a function.
--
-- This style of explaining the meaning of terms is called a **small-step operational semantics**.
-- If M —→ N, we say that term M reduces to term N, or equivalently, term M steps to term N.
-- Each compatibility rule has another reduction rule in its premise; so a step always consists
-- of a beta rule, possibly adjusted by zero or more compatibility rules.

_ : (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") —→ (ƛ "x" ⇒ ` "x")
_ = β-ƛ V-ƛ

_ : (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") —→ (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x")
_ = ξ-·₁ (β-ƛ V-ƛ)

_ : twoᶜ · sucᶜ · `zero —→ (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero
_ = ξ-·₁ (β-ƛ V-ƛ)

------------------------------------------
-- Reflexive and transitive closure

