{-

Part 1: The interval and path types

• The interval in Cubical Agda
• Path and PathP types
• Function extensionality
• Equality in Σ-types

-}

-- To make Agda cubical add the following options
{-# OPTIONS --cubical #-}
module Part1 where

-- To load a file in Agda type "C-c C-l" in emacs (the notation "C-"
-- means that one should press "CTRL", for more documentation about
-- emacs keybindings see:
-- https://www.gnu.org/software/emacs/manual/html_node/efaq/Basic-keys.html)

-- The "Core" package of the agda/cubical library sets things for us
open import Cubical.Core.Primitives public

-- The "Foundations" package contains a lot of important results (in
-- particular the univalence theorem). As we will develop many things
-- from scratch we don't import it here, but a typical file in the
-- library would import the relevant files which it uses.
--
-- open import Cubical.Foundations.Everything

-- Documentation of the Cubical Agda mode can be found at:
-- https://agda.readthedocs.io/en/v2.6.1.3/language/cubical.html


------------------------------------------------------------------------------
--                             Agda Basic                                   --
------------------------------------------------------------------------------

-- We parametrize everything by a universe level ℓ (as opposed to Coq
-- we always have to give these explicitly unless we work with the
-- lowest universe)
variable
  ℓ : Level

-- Universes in Agda are called "Set ℓ", but in order to avoid
-- confusion with h-sets we rename them to "Type ℓ".

-- Functions in Agda are written using equations as follows:
id : {A : Type ℓ} → A → A
id x = x
-- The {A : Type} notation says that A is an implicit argument Type ℓ
-- We could also write this using a λ-abstraction:

id' : {A : Type ℓ} → A → A
id' = λ x → x
-- To input a fancy symbol for the lambda write "\lambda". Agda
-- support Unicode symbols natively:
-- https://agda.readthedocs.io/en/latest/tools/emacs-mode.html#unicode-input

-- We can build Agda terms interactively in emacs by writing a ? as RHS
--
-- id'' : {A : Type ℓ} → A → A
-- id'' = ?
--
-- Try uncommenting this and pressing "C-c C-l". This will give us a
-- hole and by entering it with the cursor we can get information
-- about what Agda expects us to provide and get help from Agda in
-- providing this.
--
-- By pressing "C-c C-," while having the cursor in the goal Agda
-- shows us the current context and goal. As we're trying to write a
-- function we can press "C-c C-r" (for refine) to have Agda write the
-- λ-abstraction automatically for us. If one presses "C-c C-," in the
-- hole again "x : A" will now be in the context. If we type "x" in
-- the hole and press "C-c C-." Agda will show us that we have an A,
-- which is exactly what we want to provide to fill the goal. By
-- pressing "C-c C-SPACE" Agda will then fill the hole with "x" for us.
--
-- Agda has lots of handy commands like this for manipulating goals:
-- https://agda.readthedocs.io/en/latest/tools/emacs-mode.html#commands-in-context-of-a-goal

-- A good resource to get start with Agda is the documentation:
-- https://agda.readthedocs.io/en/latest/getting-started/index.html





------------------------------------------------------------------------------
--                     The interval and path types                          --
------------------------------------------------------------------------------


-- The interval in Cubical Agda is written I and the endpoints i0 and
-- i1 (for "interval 0" and "interval 1")

-- We can apply a function out of the interval to an endpoint just
-- like we would for any Agda function:
apply0 : (A : Type ℓ) (p : I → A) → A
apply0 A p = p i0

-- A path x ≡ y is just a function p : I → A such that p i0/i1 is definitionally x/y

-- We can write paths using λ-abstraction
path1 : {A : Type ℓ} (x : A) → x ≡ x
path1 x = λ i → x
-- Agda now checks that whatever we write as our path matches the
-- endpoints of the type that we have written

-- path1 hence gives us a proof reflexivity, let's give it a nicer
-- name and more implicit arguments:
refl : {A : Type ℓ} {x : A} → x ≡ x
refl {x = x} = λ i → x
-- The notation {x = x} lets us access the implicit argument x (left x)
-- and rename it to x (right x) in the body of refl

-- cong has a direct proof
-- TODO: what did the others call this?
cong : {A B : Type ℓ} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f p i = f (p i)

-- function extensionality also has a direct proof.
-- It also has computational content: swap the arguments.
funExt : {A B : Type ℓ} {f g : A → B} (p : (x : A) → f x ≡ g x) → f ≡ g
funExt p i x = p x i

-- TODO: add sym


-- Dependent paths: PathP

-- In general PathP A x y has A : I → Type, x : A i0 and y : A i1
-- PathP = Dependent paths (Path over a Path)

-- In fact, x ≡ y is short for PathP (λ _ → A) x y
refl' : {A : Type ℓ} (x : A) → PathP (λ _ → A) x x
refl' x = λ _ → x

-- We cannot pattern-match on interval variables as I is not inductively defined
-- foo : {A : Type} → I → A
-- foo r = {!r!}   -- Try typing C-c C-c

