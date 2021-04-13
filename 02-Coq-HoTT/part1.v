(** The HoTT Library: A formalization of homotopy type theory in Coq, 

        Andrej Bauer, Jason Gross, Peter LeFanu Lumsdaine, 
        Mike Shulman, Matthieu Sozeau, Bas Spitters, 

                           2016 CPP17
           http://doi.acm.org/10.1145/3018610.3018615

Started at IAS '12. Initially based on Voevodsky's UniMath library
And many contributions since then...
         Gaetan Gilbert, Andreas Lynge, Ali Caglayan, Dan Christensen, ...

                   https://github.com/HoTT/HoTT *)



(** Part 1. Quick intro to Coq

Please check the intro material
https://coq.inria.fr/documentation
(e.g. Andrej's lectures or software foundations )

Emacs/Proof general/company-coq
https://github.com/cpitclaudel/company-coq *)



(** Coq

CoC: Calculus of Constructions, 
Coquand (Inventor of CoC)
Rooster is French national symbol. Programming languages named after animals: Caml, ...

*)
(* Stale French joke about american cultural imperialism *)

(** Coq is an industry strength proof assistant with thousands of users.
    It's been used both for mathematics and computer science *)



(** 
CoC -> pCuIC
predicative Calculus of universe polymorphic Inductive Constructions 
Let's pretend it is MLTT (as in day1)
Logical framework *)

Require Import Basics. (* HoTT disables the stdlib. Let's import some notations -> *)

(* Pi-types are build-in in Coq *)
Variable P:nat -> Type. (* -> is notation for non-dependent forall *)
Check forall n:nat, P n.

(** Other connective are defined as inductive types... *)

(** Inductive types
Coq has syntactic check whether an inductive type is well-defined, unlike agda's termination checker *)

(* Introduction, recursion, induction, computation *)

Module Prod.
(* We use Coq's modules to avoid poluting the namespace. *)
  
(* https://github.com/HoTT/HoTT/blob/master/STYLE.md#induction-and-recursion-principles *)
Local Unset Elimination Schemes.
Inductive prod (A B:Type) : Type :=
  pair : A -> B -> prod A B.
(** Coq has a powerful notation system. 
    Scopes allow us to reuse notations in different context.
    Here we avoid conflicts with multiplication on the naturals. *)
Notation "A * B" := (prod A B) : type_scope.
Notation "( a , b )" := (pair _ _ a b).

Scheme prod_rec := Minimality for prod Sort Type.
Scheme prod_ind := Induction for prod Sort Type.

Check prod_rec.
(** prod_rec
     : forall A B P : Type, (A -> B -> P) -> A * B -> P *)

Check prod_ind. (* dependent recursion *)
(** prod_ind
     : forall (A B : Type) (P : A * B -> Type), (forall (a : A) (b : B), P (pair A B a b)) -> forall p : A * B, P p *)


(** Coq uses sections for manage name spaces *)
Section projections.

  Variables A B : Type.

  Definition fst (p:A * B) := match p with (pair x y) => x end.
  Definition snd (p:A * B) := match p with (pair x y) => y end.

(** Coq can derive the types A B *)  
Goal forall a b, fst (a, b)=a.
reflexivity. (** computation *)
Qed.

Goal forall (p:A * B), (fst p, snd p)=p.
Fail reflexivity. (** we do not have the eta rule *)
Abort.
End projections.
End Prod. (* close the Module. Notations disappear. *)

(** Definition in the HoTT library: *)

Print prod.
(** Record prod (A B : Type) : Type := pair { fst : A;  snd : B }
prod has primitive projections with eta conversion. *)

Variables A B : Type.

Goal forall (p:A * B), (fst p, snd p)=p.
reflexivity. (** we do have the eta rule *)
Qed.

(** Exercise: write the inductive definition for sum-Types. *)
(* Print sum. *)

Print sig. (** We use the same method as for prod *)
(* Record sig (A : Type) (P : A -> Type) : Type := exist { proj1 : A;  proj2 : P proj1 }
sig has primitive projections with eta conversion.*)

(* Exercise: Write, or find the induction principles for Empty, Unit, bool, nat *)
Print Type0. (* This is the lowest universe in the HoTT library. It is called Set in Coq. *)
Print Empty.
(* No constructors. 
Inductive Empty@{} : Type0 :=  

No universe dependencies. @{} *)

Print Unit.
Print nat.

Require Import Bool. (* We load Bool from the HoTT library *)
(* https://github.com/HoTT/HoTT/blob/master/theories/Types/Bool.v *)
Print Bool.

Locate paths.
(* HoTT.Basics.Overture
This is a cumulative collection of inductive definitions, one for each universe level.
Cumulative Inductive paths {A : Type} (a : A) : A -> Type :=
  idpath : paths a a. *)

Print paths.
(* Inductive paths@{u} (A : Type) (a : A) : A -> Type :=  idpath : a = a *)
(** We do not use Coq's id-type as it is defined to be in the lowest universe Prop.
    This would break HoTT. This is where we use Coq's indices matter flag. *)

(* Exercise. Do the exercise from day1 in Coq.
    Given a type family P : A → B → U, inhabit the type (Π (x : A) Σ (y : B) P x y) → Σ (f : A → B) Π (x : A) P x (f x).
    Define addition and multiplication on N using recursion
*)

(** Universes in Coq
are slightly different than in MLTT.
They are Russel style. 
https://ncatlab.org/homotopytypetheory/show/universe
A universe a la Russell is a type whose terms are types. *)

Section Universes.

Print Universes. (** Coq'd Prop still exists, but we don't use it. *)

(** This would lead to the Girard paradox.*)
Check Type:Type.
(** However, this is syntactic sugar for *)

Universe i j.
Print Universes.
Check Type@{i}:Type@{j}. (* Coq checks that the constraint i<j is consisent with the others.*)

(* This is not allowed: *)
Fail Definition test:Type@{i}:= Type@{i}.

(* But this is: *)
Definition test:Type@{i}:=Type@{j}.
Definition test2:Type@{i}:=forall A:Type@{j}, A->Type@{j}.

Universe Ularge Uhuge.
Constraint Ularge < Uhuge. (* We can also add the constraints by hand. *)
Check Type@{Ularge}:Type@{Ularge+1}.
Check Type@{Ularge}:Type@{Uhuge}.    (* Coq's universes are cumulative ULarge+1<=Uhuge *)
Fail Check Type@{Uhuge}:Type@{Ularge}. 
End  Universes.


(** HoTT-library *)

(** Bird's eye view of the HoTT library
    Do try to play along, and make the exercises. *)

(** We use Coq without the stdlib, So, we develop our own *)
(** For an overview of the library see: 
    https://github.com/HoTT/HoTT/wiki
    Especially, the beautiful pictures. *)

(** Basics
     Our stdlib is in the Basics dir:
       https://github.com/HoTT/HoTT/tree/master/theories/Basics
     Our Prelude:                         
         https://github.com/HoTT/HoTT/blob/master/theories/Basics/Overture.v
     E.g. Notations are defined here.
 *)
Require Import Basics.

(** For a good overview of the library:
    https://github.com/HoTT/HoTT/blob/master/STYLE.md
    *)

(** Design principles:
    Core library should be accessible, 
    limited use of unicode, canonical structures, type classes, ... *)

(** Connection with the HoTT book
http://hott.github.io/HoTT/coqdoc-html/HoTTBook.html

(Hint: there are still some lemmas missing :-)  )

It would be interesting to link Egbert's book to the HoTT library in a similar way. *)

(** Slides  *)




(** Let's dive into some computation with paths.
    Paths form a proof-relevant equivalence relation, a groupoid.
    Technically, an infinity groupoid.
    A quick guided tour.

** Path groupoids *)
Require Import PathGroupoids.

(* Notations from Day1 *)
Locate "#".
Locate transport. (* From Overture *)

(* From Overture: *)
(** The inverse of a path. *)
Definition inverse {A : Type} {x y : A} (p : x = y) : y = x
  := match p with idpath => idpath end.
Definition concat {A : Type} {x y z : A} (p : x = y) (q : y = z) : x = z :=
  match p, q with idpath, idpath => idpath end.

(** The identity path. *)
Notation "1" := idpath : path_scope.

(** The composition of two paths. *)
Notation "p @ q" := (concat p%path q%path) : path_scope.

(** The inverse of a path. *)
Notation "p ^" := (inverse p%path) : path_scope.

Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y :=
  match p with idpath => u end.

(** Transport is very common so it is worth introducing a parsing notation for it.  However, we do not use the notation for output because it hides the fibration, and so makes it very hard to read involved transport expression.*)

Notation "p # x" := (transport _ p x) (only parsing) : path_scope.

(** Functions act on paths: if [f : A -> B] and [p : x = y] is a path in [A], then [ap f p : f x = f y].

   We typically pronounce [ap] as a single syllable, short for "application"; 
   but it may also be considered as an acronym, "action on paths". *)

Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y
  := match p with idpath => idpath end.


(** Pathgroupoids.v *)

(* Note the elaborate naming scheme. *)

(** ** The 1-dimensional groupoid structure. *)

(** Most proofs are direct by path induction. *)
(** Inverse distributes over concatenation *)

(* Custom tactics: 
   with_rassoc this is easier then writing proof terms *)

(** *** Functoriality of functions *)

(** Here we prove that functions behave like functors between groupoids, and that [ap] itself is functorial. *)

(** The Eckmann-Hilton argument 
The composition operation on the second loop space is commutative.
See the HoTTbook 2.1.6, where the proof takes 1.5pp!
*)
Print eckmann_hilton.

(** hott_simpl tactic. 
Try to rewrite with a hopefully confluent rewrite system, and then solve the remaining goal using proof search. *)

(* Exercises:
https://github.com/HoTT/EPIT-2020/blob/main/01-introduction-to-hott/exercises.v
Do the exercises of Day1 on identity types, or look them up in the library. *)
