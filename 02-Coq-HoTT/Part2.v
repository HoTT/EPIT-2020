(** Part 2: HoTT-library *)

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
