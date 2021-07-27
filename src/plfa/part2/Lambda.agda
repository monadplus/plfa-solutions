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
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.String using (String; _≟_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋; False; toWitnessFalse)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import plfa.part1.Isomorphism using (_≲_; _≃_; extensionality)

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

infix  5  ƛ_⇒_   -- \Gl-
infix  5  μ_⇒_   -- \mu
infixl 7  _·_     -- \cdot
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
_[ƛ_,_:=_]′ : Term → Id → Id → Term → Term

N [ƛ x , y := V ]′ with x ≟ y
... | yes _           = N
... | no _            = N [ y := V ]′

(` x) [ y := V ]′ with x ≟ y
... | yes _          =  V
... | no  _          =  ` x
(ƛ x ⇒ N) [ y := V ]′ = ƛ x ⇒ N [ƛ x , y := V ]′
(L · M) [ y := V ]′   =  L [ y := V ]′ · M [ y := V ]′
(`zero) [ y := V ]′   =  `zero
(`suc M) [ y := V ]′  =  `suc M [ y := V ]′
(case L [zero⇒ M |suc x ⇒ N ]) [ y := V ]′ =
  case L [ y := V ]′ [zero⇒ M [ y := V ]′ |suc x ⇒ N [ƛ x , y := V ]′ ]
(μ x ⇒ N) [ y := V ]′ = μ x ⇒ N [ƛ x , y := V ]′

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

-- A single step is only part of the story. In general, we wish to repeatedly step a closed term until it reduces to a value.
-- We do this by defining the reflexive and transitive closure —↠ of the step relation —→.
--
-- We define reflexive and transitive closure as a sequence of zero or more steps of the underlying relation.

infix  2 _—↠_ -- \em\rr-
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ : Term → Term → Set where
  _∎ : ∀ M
      ---------
    → M —↠ M

  _—→⟨_⟩_ : ∀ L {M N}
    → L —→ M
    → M —↠ N
      ---------
    → L —↠ N

begin_ : ∀ {M N}
  → M —↠ N
    ------
  → M —↠ N
begin M—↠N = M—↠N

—↠-trans : ∀ {M L N} → M —↠ L → L —↠ N → M —↠ N
—↠-trans (_ ∎) M—↠N = M—↠N
—↠-trans {M} {L} {N} (_ —→⟨ M—↠L₁ ⟩ L₁—↠L) L—↠N = M —→⟨ M—↠L₁ ⟩ —↠-trans L₁—↠L L—↠N

-- We can read this as follows:
--
-- * From term M, we can take no steps, giving a step of type M —↠ M. It is written M ∎.
-- * From term L we can take a single step of type L —→ M followed by zero or more steps of type M —↠ N,
--   giving a step of type L —↠ N. It is written L —→⟨ L—→M ⟩ M—↠N, where L—→M and M—↠N are steps
--   of the appropriate type.


-- An alternative is to define reflexive and transitive closure directly,
-- as the smallest relation that includes —→ and is also reflexive and transitive.
--
-- We could do so as follows:

data _—↠′_ : Term → Term → Set where

  step′ : ∀ {M N}
    → M —→ N
      -------
    → M —↠′ N

  refl′ : ∀ {M}
      -------
    → M —↠′ M

  trans′ : ∀ {L M N}
    → L —↠′ M
    → M —↠′ N
      -------
    → L —↠′ N

-- The three constructors specify, respectively, that —↠′ includes —→ and is reflexive and transitive.

—↠≲—↠′ : ∀ {M N : Term} → M —↠ N ≲ M —↠′ N
—↠≲—↠′ =
  record
    { to = to
    ; from = from
    ; from∘to = from∘to
    }
  where

  to : ∀ {M N : Term} → M —↠ N → M —↠′ N
  to (M ∎) = refl′
  to (M₁ —→⟨ M₁—→M₂ ⟩ M₂—↠N) = trans′ (step′ M₁—→M₂) (to M₂—↠N)

  from : ∀ {M N : Term} → M —↠′ N → M —↠ N
  from {M} {N} (step′ M—→N) = M —→⟨ M—→N ⟩ N ∎
  from {M} {N} refl′ = M ∎
  from {M} {N} (trans′ M—↠′M₂ M₂—↠′N) = —↠-trans (from M—↠′M₂) (from M₂—↠′N)

  from∘to : ∀ {M N : Term} (x : M —↠ N) → from (to x) ≡ x
  from∘to (M ∎) = refl
  from∘to (M —→⟨ M—→M₁ ⟩ M₁—↠N) rewrite from∘to M₁—↠N = refl

---------------------------
-- Confluence

-- One important property a reduction relation might satisfy is to be *confluent*.
-- If term L reduces to two other terms, M and N, then both of these reduce to a common term P.
-- It can be illustrated as follows:

--            L
--           / \
--          /   \
--         /     \
--        M       N
--         \     /
--          \   /
--           \ /
--            P

-- Here L, M, N are universally quantified while P is existentially quantified.
-- If each line stands for zero or more reduction steps, this is called confluence,
-- while if the top two lines stand for a single reduction step and the bottom two stand for
-- zero or more reduction steps it is called the diamond property.

postulate
  confluence : ∀ {L M N}
    → ((L —↠ M) × (L —↠ N))
      --------------------
    → ∃[ P ] ((M —↠ P) × (N —↠ P))

  diamond : ∀ {L M N}
    → ((L —→ M) × (L —→ N))
      --------------------
    → ∃[ P ] ((M —↠ P) × (N —↠ P))

-- The reduction system studied in this chapter is deterministic.
-- In symbols:

postulate
  deterministic : ∀ {L M N}
    → L —→ M
    → L —→ N
      ------
    → M ≡ N

-- It is easy to show that every deterministic relation satisfies the diamond and confluence properties.
-- Hence, all the reduction systems studied in this text are trivially confluent.

----------------------------
-- Examples

-- The Church numeral two applied to the successor function and zero yields the natural number two:

_ : twoᶜ · sucᶜ · `zero —↠ `suc `suc `zero
_ =
  begin
    twoᶜ · sucᶜ · `zero
  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero
  —→⟨ β-ƛ V-zero ⟩
    sucᶜ · (sucᶜ · `zero)
  —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    sucᶜ · `suc `zero
  —→⟨ β-ƛ (V-suc V-zero) ⟩
    `suc (`suc `zero)
  ∎

--  Here is a sample reduction demonstrating that two plus two is four:

_ : plus · two · two —↠ `suc `suc `suc `suc `zero
_ =
  begin
    plus · two · two
  —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
    (ƛ "m" ⇒ ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
        · two · two
  —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
    (ƛ "n" ⇒
      case two [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
         · two
  —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
    case two [zero⇒ two |suc "m" ⇒ `suc (plus · ` "m" · two) ]
  —→⟨ β-suc (V-suc V-zero) ⟩
    `suc (plus · `suc `zero · two)
  -- The same as before with ξ-suc ... --
  —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
    `suc ((ƛ "m" ⇒ ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
        · `suc `zero · two)
  —→⟨ ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
    `suc ((ƛ "n" ⇒
      case `suc `zero [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
        · two)
  —→⟨ ξ-suc (β-ƛ (V-suc (V-suc V-zero))) ⟩
    `suc (case `suc `zero [zero⇒ two |suc "m" ⇒ `suc (plus · ` "m" · two) ])
  —→⟨ ξ-suc (β-suc V-zero) ⟩
    `suc `suc (plus · `zero · two)
  -- The same as before with ξ-suc (ξ-suc ...) --
  —→⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
    `suc `suc ((ƛ "m" ⇒ ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
        · `zero · two)
  —→⟨ ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero))) ⟩
    `suc `suc ((ƛ "n" ⇒
      case `zero [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
        · two)
  —→⟨ ξ-suc (ξ-suc (β-ƛ (V-suc (V-suc V-zero)))) ⟩
    `suc `suc (case `zero [zero⇒ two |suc "m" ⇒ `suc (plus · ` "m" · two) ])
  —→⟨ ξ-suc (ξ-suc β-zero) ⟩
    `suc (`suc (`suc (`suc `zero)))
  ∎

--  And here is a similar sample reduction for Church numerals:

_ : plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero —↠ `suc `suc `suc `suc `zero
_ =
  begin
    (ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒ ` "m" · ` "s" · (` "n" · ` "s" · ` "z"))
      · twoᶜ · twoᶜ · sucᶜ · `zero
  —→⟨ ξ-·₁ (ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ))) ⟩
    (ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒ twoᶜ · ` "s" · (` "n" · ` "s" · ` "z"))
      · twoᶜ · sucᶜ · `zero
  —→⟨ ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
    (ƛ "s" ⇒ ƛ "z" ⇒ twoᶜ · ` "s" · (twoᶜ · ` "s" · ` "z")) · sucᶜ · `zero
  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒ twoᶜ · sucᶜ · (twoᶜ · sucᶜ · ` "z")) · `zero
  —→⟨ β-ƛ V-zero ⟩
    twoᶜ · sucᶜ · (twoᶜ · sucᶜ · `zero)
  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · (twoᶜ · sucᶜ · `zero)
  —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · ((ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero)
  —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · (sucᶜ · (sucᶜ · `zero))
  —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (β-ƛ V-zero)) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · (sucᶜ · (`suc `zero))
  —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc V-zero)) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · (`suc `suc `zero)
  —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
    sucᶜ · (sucᶜ · `suc `suc `zero)
  —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero))) ⟩
    sucᶜ · (`suc `suc `suc `zero)
  —→⟨ β-ƛ (V-suc (V-suc (V-suc V-zero))) ⟩
   `suc (`suc (`suc (`suc `zero)))
  ∎

one : Term
one = `suc `zero

plus-example : plus · one · one —↠ `suc `suc `zero
plus-example =
  begin
    plus · one · one
  —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
    (ƛ "m" ⇒ ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
        · one · one
  —→⟨ ξ-·₁ (β-ƛ (V-suc V-zero)) ⟩
    (ƛ "n" ⇒
      case one [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
        · one
  —→⟨ β-ƛ (V-suc V-zero) ⟩
    case one [zero⇒ one |suc "m" ⇒ `suc (plus · ` "m" · one) ]
  —→⟨ β-suc V-zero ⟩
    `suc (plus · `zero · one)
  -- same as before --
  —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
    `suc ((ƛ "m" ⇒ ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
        · `zero · one)
  —→⟨ ξ-suc (ξ-·₁ (β-ƛ V-zero)) ⟩
    `suc ((ƛ "n" ⇒
      case `zero [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
        · one)
  —→⟨ ξ-suc (β-ƛ (V-suc V-zero)) ⟩
    `suc (case `zero [zero⇒ one |suc "m" ⇒ `suc (plus · ` "m" · one) ])
  —→⟨ ξ-suc (β-zero) ⟩
    `suc one
  ∎

----------------------------------------------------
-- Syntax of types

-- We have just two types:
--     Functions, A ⇒ B
--     Naturals, `ℕ
-- As before, to avoid overlap we use variants of the names used by Agda.

-- Here is the syntax of types in BNF:
--   A, B, C  ::=  A ⇒ B | `ℕ
-- And here it is formalised in Agda:

infixr 7 _⇒_

data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ : Type

-- Precedence:
--  (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ stands for ((`ℕ ⇒ `ℕ) ⇒ (`ℕ ⇒ `ℕ)).
--  plus · two · two stands for (plus · two) · two.

-- Quiz:

-- ƛ "s" ⇒ ` "s" · (` "s"  · `zero) of type (`ℕ ⇒ `ℕ) ⇒ `ℕ

-- (ƛ "s" ⇒ ` "s" · (` "s"  · `zero)) · sucᶜ of type `ℕ

------------------------
-- Typing

-- While reduction considers only closed terms, typing must consider terms with free variables.
-- To type a term, we must first type its subterms, and in particular in the body of an abstraction
-- its bound variable may appear free.

-- A context associates variables with types.
-- We let Γ and Δ range over contexts.
-- We write ∅ for the empty context, and Γ , x ⦂ A for the context that extends Γ by mapping variable x to type A.
--
-- For example,
--
--     ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ
--
-- is the context that associates variable "s" with type `ℕ ⇒ `ℕ, and variable "z" with type `ℕ.

-- Contexts are formalised as follows:

infixl 5  _,_⦂_

data Context : Set where
  ∅     : Context -- \0
  _,_⦂_ : Context → Id → Type → Context -- \: and move to the right

Context-≃ : Context ≃ List (Id × Type)
Context-≃ =
  record
    { to = to
    ; from = from
    ; from∘to = from∘to
    ; to∘from = to∘from
    }
  where

  to : Context → List (Id × Type)
  to ∅ = []
  to (Γ , x ⦂ σ) = ⟨ x , σ ⟩ ∷ to Γ

  from : List (Id × Type) → Context
  from [] = ∅
  from (⟨ x , σ ⟩ ∷ xs) = (from xs), x ⦂ σ

  from∘to : ∀ (x : Context) → from (to x) ≡ x
  from∘to ∅ = refl
  from∘to (ctx , x ⦂ x₁) rewrite from∘to ctx = refl

  to∘from : ∀ (x : List (Id × Type)) → to (from x) ≡ x
  to∘from [] = refl
  to∘from (⟨ fst , snd ⟩ ∷ xs) rewrite to∘from xs = refl

---------------------------------------------------------
-- Lookup judgment

-- We have two forms of judgment. The first is written

-- Γ ∋ x ⦂ A

-- and indicates in context Γ that variable x has type A. It is called lookup. For example,

--     ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ∋ "z" ⦂ `ℕ
--     ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ∋ "s" ⦂ `ℕ ⇒ `ℕ

-- give us the types associated with variables "z" and "s", respectively.
-- The symbol ∋ (pronounced “ni”, for “in” backwards) is chosen because checking
-- that Γ ∋ x ⦂ A is analogous to checking whether x ⦂ A appears in a list corresponding to Γ.

-- If two variables in a context have the same name, then lookup should return the most recently bound variable,
-- which shadows the other variables. For example,

--     ∅ , "x" ⦂ `ℕ ⇒ `ℕ , "x" ⦂ `ℕ ∋ "x" ⦂ `ℕ.

-- Here "x" ⦂ `ℕ ⇒ `ℕ is shadowed by "x" ⦂ `ℕ.

-- Lookup is formalised as follows:

infix  4  _∋_⦂_ -- ∋ \ni

data _∋_⦂_ : Context → Id → Type → Set where

  Z : ∀ {Γ x A}
      ------------------
    → Γ , x ⦂ A ∋ x ⦂ A

  S : ∀ {Γ x y A B}
    → x ≢ y
    → Γ ∋ x ⦂ A
      ------------------
    → Γ , y ⦂ B ∋ x ⦂ A

-- The constructors Z and S correspond roughly to the constructors here and there for the element-of relation _∈_ on lists.
--
-- Constructor S takes an additional parameter, which ensures that when we look up a variable
-- that it is not shadowed by another variable with the same name to its left in the list.

-- It can be rather tedious to use the S constructor, as you have to provide proofs that x ≢ y each time. For example:

_ : ∅ , "x" ⦂ `ℕ ⇒ `ℕ , "y" ⦂ `ℕ , "z" ⦂ `ℕ ∋ "x" ⦂ `ℕ ⇒ `ℕ
_ = S (λ()) (S (λ()) Z)

-- Instead, we’ll use a “smart constructor”, which uses proof by reflection to check the inequality while type checking:

S′ : ∀ {Γ x y A B}
   → {x≢y : False (x ≟ y)}
   → Γ ∋ x ⦂ A
     ------------------
   → Γ , y ⦂ B ∋ x ⦂ A

S′ {x≢y = x≢y} x = S (toWitnessFalse x≢y) x

-------------------------------
-- Typing judgment

-- The second judgment is written

-- Γ ⊢ M ⦂ A

-- and indicates in context Γ that term M has type A. Context Γ provides types for all the free variables in M. For example:

--     ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "z" ⦂ `ℕ
--     ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "s" ⦂ `ℕ ⇒ `ℕ
--     ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "s" · ` "z" ⦂  `ℕ
--     ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "s" · (` "s" · ` "z") ⦂  `ℕ
--     ∅ , "s" ⦂ `ℕ ⇒ `ℕ ⊢ ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ⦂  `ℕ ⇒ `ℕ
--     ∅ ⊢ ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ⦂  (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ

-- Typing is formalised as follows:

infix  4  _⊢_⦂_ -- ⊢ \vdash

data _⊢_⦂_ : Context → Term → Type → Set where

  -- Axiom
  ⊢` : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
      -----------
    → Γ ⊢ ` x ⦂ A

  -- ⇒-I
  ⊢ƛ : ∀ {Γ x N A B}
    → Γ , x ⦂ A ⊢ N ⦂ B
      -------------------
    → Γ ⊢ ƛ x ⇒ N ⦂ A ⇒ B

  -- ⇒-E
  _·_ : ∀ {Γ L M A B}
    → Γ ⊢ L ⦂ A ⇒ B
    → Γ ⊢ M ⦂ A
      -------------
    → Γ ⊢ L · M ⦂ B

  -- ℕ-I₁
  ⊢zero : ∀ {Γ}
      --------------
    → Γ ⊢ `zero ⦂ `ℕ

  -- ℕ-I₂
  ⊢suc : ∀ {Γ M}
    → Γ ⊢ M ⦂ `ℕ
      ---------------
    → Γ ⊢ `suc M ⦂ `ℕ

  -- ℕ-E
  ⊢case : ∀ {Γ L M x N A}
    → Γ ⊢ L ⦂ `ℕ
    → Γ ⊢ M ⦂ A
    → Γ , x ⦂ `ℕ ⊢ N ⦂ A
      -------------------------------------
    → Γ ⊢ case L [zero⇒ M |suc x ⇒ N ] ⦂ A

  ⊢μ : ∀ {Γ x M A}
    → Γ , x ⦂ A ⊢ M ⦂ A
      -----------------
    → Γ ⊢ μ x ⇒ M ⦂ A

-- Each type rule is named after the constructor for the corresponding term.

-- Most of the rules have a second name, derived from a convention in logic,
-- whereby the rule is named after the type connective that it concerns;
-- rules to introduce and to eliminate each connective are labeled -I and -E, respectively.

-- Note also the three places (in ⊢ƛ, ⊢case, and ⊢μ) where the context is extended with x and an appropriate type,
-- corresponding to the three places where a bound variable is introduced.

-- The rules are deterministic, in that at most one rule applies to every term.

----------------------------------------
-- Example type derivations

-- Type derivations correspond to trees. In informal notation, here is a type derivation for the Church numeral two,

{-
                        ∋s                     ∋z
                        ------------------ ⊢`  -------------- ⊢`
∋s                      Γ₂ ⊢ ` "s" ⦂ A ⇒ A     Γ₂ ⊢ ` "z" ⦂ A
------------------ ⊢`   ------------------------------------- _·_
Γ₂ ⊢ ` "s" ⦂ A ⇒ A      Γ₂ ⊢ ` "s" · ` "z" ⦂ A
---------------------------------------------- _·_
Γ₂ ⊢ ` "s" · (` "s" · ` "z") ⦂ A
-------------------------------------------- ⊢ƛ
Γ₁ ⊢ ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ⦂ A ⇒ A
------------------------------------------------------------- ⊢ƛ
Γ ⊢ ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ⦂ (A ⇒ A) ⇒ A ⇒ A


where ∋s and ∋z abbreviate the two derivations,

             ---------------- Z
"s" ≢ "z"    Γ₁ ∋ "s" ⦂ A ⇒ A
----------------------------- S       ------------- Z
Γ₂ ∋ "s" ⦂ A ⇒ A                       Γ₂ ∋ "z" ⦂ A

and where Γ₁ = Γ , "s" ⦂ A ⇒ A and Γ₂ = Γ , "s" ⦂ A ⇒ A , "z" ⦂ A.

The typing derivation is valid for any Γ and A, for instance, we might take Γ to be ∅ and A to be `ℕ.
-}

-- Here is the above typing derivation formalised in Agda:

Ch : Type → Type
Ch A = (A ⇒ A) ⇒ A ⇒ A

⊢twoᶜ : ∀ {Γ A} → Γ ⊢ twoᶜ ⦂ Ch A
⊢twoᶜ = ⊢ƛ (⊢ƛ (⊢` ∋s · (⊢` ∋s · ⊢` ∋z)))
  where
  ∋s = S′ Z
  ∋z = Z

--  Here are the typings corresponding to computing two plus two:

⊢two : ∀ {Γ} → Γ ⊢ two ⦂ `ℕ
⊢two = ⊢suc (⊢suc ⊢zero)

⊢plus : ∀ {Γ} → Γ ⊢ plus ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ
⊢plus = ⊢μ (⊢ƛ (⊢ƛ (⊢case (⊢` ∋m) (⊢` ∋n)
         (⊢suc (⊢` ∋+ · ⊢` ∋m′ · ⊢` ∋n′)))))
  where
  -- S′ marks the position in the context
  --  ⊢μ, ⊢ƛ, ⊢case add new position
  ∋+  = S′ (S′ (S′ Z))
  ∋m  = S′ Z
  ∋n  = Z
  ∋m′ = Z
  ∋n′ = S′ Z

⊢2+2 : ∅ ⊢ plus · two · two ⦂ `ℕ
⊢2+2 = ⊢plus · ⊢two · ⊢two

-------------------------------------
-- Interaction with Agda

{-
Construction of a type derivation may be done interactively. Start with the declaration:

  ⊢sucᶜ : ∅ ⊢ sucᶜ ⦂ `ℕ ⇒ `ℕ
  ⊢sucᶜ = ?

Typing C-c C-l causes Agda to create a hole and tell us its expected type:

  ⊢sucᶜ = { }0
  ?0 : ∅ ⊢ sucᶜ ⦂ `ℕ ⇒ `ℕ

Now we fill in the hole by typing C-c C-r.
Agda observes that the outermost term in sucᶜ is ƛ, which is typed using ⊢ƛ.
The ⊢ƛ rule in turn takes one argument, which Agda leaves as a hole:

  ⊢sucᶜ = ⊢ƛ { }1
  ?1 : ∅ , "n" ⦂ `ℕ ⊢ `suc ` "n" ⦂ `ℕ

We can fill in the hole by typing C-c C-r again:

  ⊢sucᶜ = ⊢ƛ (⊢suc { }2)
  ?2 : ∅ , "n" ⦂ `ℕ ⊢ ` "n" ⦂ `ℕ

And again:

  ⊢sucᶜ = ⊢ƛ (⊢suc (⊢` { }3))
  ?3 : ∅ , "n" ⦂ `ℕ ∋ "n" ⦂ `ℕ

A further attempt with C-c C-r yields the message:

  Don't know which constructor to introduce of Z or S

We can fill in Z by hand. If we type C-c C-space, Agda will confirm we are done:

  ⊢sucᶜ = ⊢ƛ (⊢suc (⊢` Z))

The entire process can be automated using Agsy, invoked with C-c C-a.
Chapter Inference will show how to use Agda to compute type derivations directly.
-}

⊢sucᶜ : ∅ ⊢ sucᶜ ⦂ `ℕ ⇒ `ℕ
⊢sucᶜ = ⊢ƛ (⊢suc (⊢` Z))

--------------------------------------
-- Lookup is injective

-- The lookup relation Γ ∋ x ⦂ A is injective, in that for each Γ and x there is at most one A such that the judgment holds:

∋-injective : ∀ {Γ x A B} → Γ ∋ x ⦂ A → Γ ∋ x ⦂ B → A ≡ B
∋-injective Z        Z          =  refl
∋-injective Z        (S x≢ _)   =  ⊥-elim (x≢ refl)
∋-injective (S x≢ _) Z          =  ⊥-elim (x≢ refl)
∋-injective (S _ ∋x) (S _ ∋x′)  =  ∋-injective ∋x ∋x′

-- The typing relation Γ ⊢ M ⦂ A is not injective.
--
-- For example, in any Γ the term ƛ "x" ⇒ ` "x" has type A ⇒ A for any type A.

------------------------------------------
-- Non-examples

-- We can also show that terms are not typeable.
--
-- For example, here is a formal proof that it is not possible to type the term `zero · `suc `zero.
-- It cannot be typed, because doing so requires that the first term in the application is both a natural and a function:

nope₁ : ∀ {A} → ¬ (∅ ⊢ `zero · `suc `zero ⦂ A)
nope₁ (() · _)

-- As a second example, here is a formal proof that it is not possible to type ƛ "x" ⇒ ` "x" · ` "x".
-- It cannot be typed, because doing so requires types A and B such that A ⇒ B ≡ A:

nope₂ : ∀ {A} → ¬ (∅ ⊢ ƛ "x" ⇒ ` "x" · ` "x" ⦂ A)
nope₂ (⊢ƛ (⊢` ∋x · ⊢` ∋x′))  =  contradiction (∋-injective ∋x ∋x′)
  where
  contradiction : ∀ {A B} → ¬ (A ⇒ B ≡ A)
  contradiction ()

------------
-- Quiz


_ : ∅ , "y" ⦂ `ℕ ⇒ `ℕ , "x" ⦂ `ℕ ⊢ ` "y" · ` "x" ⦂ `ℕ
_ = (⊢` (S′ Z)) · (⊢` Z)

-- ∅ , "y" ⦂ `ℕ ⇒ `ℕ , "x" ⦂ `ℕ ⊢ ` "x" · ` "y" ⦂ A
-- No such type A.

_ : ∅ , "y" ⦂ `ℕ ⇒ `ℕ ⊢ ƛ "x" ⇒ ` "y" · ` "x" ⦂ `ℕ ⇒ `ℕ
_ = ⊢ƛ (⊢` (S′ Z) · ⊢` Z)


-- Exercises

⊢mul : ∀ {Γ} → Γ ⊢ mul ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ
⊢mul = ⊢μ (⊢ƛ (⊢ƛ (⊢case (⊢` ∋m) ⊢zero
         (⊢plus · ⊢` ∋n · (⊢` ∋* · ⊢` ∋m′ · ⊢` ∋n)))))
  where
  ∋m  = S′ Z
  ∋m′ = Z
  ∋n  = S′ Z
  ∋*  = S′ (S′ (S′ Z))

Church : Type → Type
Church A = (A ⇒ A) ⇒ (A ⇒ A)

-- ⊢mulᶜ : ∀ {Γ A} → Γ ⊢ mulᶜ ⦂ Church A ⇒ Church A ⇒ Church A
-- ⊢mulᶜ = ⊢ƛ (⊢ƛ (⊢ƛ (⊢ƛ (⊢` ∋m · ⊢ƛ (∋n · ∋s · ∋x) · ⊢` ∋z))))
--   where
--   ∋m  = S′ (S′ (S′ Z))
--   ∋z  = Z
--   ∋n  = S′ (S′ (S′ Z))
--   ∋s  = S′ (S′ Z)
--   ∋x  = Z
