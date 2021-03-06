(*** Part 2: Hlevels, type classes and HITs *)
(** Tutorial on type classes (https://www.labri.fr/perso/casteran/CoqArt/TypeClassesTut/typeclassestut.pdf) *)

From HoTT Require Export Basics.

(** As we saw in day1. Propositions are closed under a number of constructions:
forall, ->, *, ..., existential quantification where the domain is a proposition.

This holds in general, hlevels are closed under:
Pi-types, Sigma-types, identity-types, and equivalences.
When n>=1, they are also closed under inductive types (W-types).

From Overture:
Notation Contr := (IsTrunc minus_two).
Notation IsHProp := (IsTrunc minus_two.+1).
Notation IsHSet := (IsTrunc minus_two.+2). *)

(** In this way we can usually easily compute the hlevel of a complex type from its components.
   This can be done conveniently using Coq's type classes.

Type classes are known from haskell, and group similar types together.
Fx. consider the Class of types with a Monoid structure.
There can be different Instances of that: (nat,+) and (nat,* )
In Coq they are implemented using dependent records and eauto search.
Usually, we'd like proofs that something has a particular hlevel to be an Instance of the type class.*)

From HoTT Require Import Overture.

Global Instance istrunc_paths (A : Type) n `{H : IsTrunc n.+1 A} (x y : A)
: IsTrunc n (x = y)
  := H x y.


(** To prove that something is a set, it suffices to prove that it's a proposition.
However, we give this low priority (1000). Why? *)

(** Truncation levels are cumulative. 
Global Instance trunc_succ `{IsTrunc n A}
  : IsTrunc n.+1 A | 1000. *)


(** In particular, a contractible type, hprop, or hset is truncated at all higher levels.*)
(*
Definition trunc_contr {n} {A} `{Contr A} : IsTrunc n.+1 A
  := (@trunc_leq (-2) n.+1 tt _ _).

Definition trunc_hprop {n} {A} `{IsHProp A} : IsTrunc n.+2 A
  := (@trunc_leq (-1) n.+2 tt _ _).

Definition trunc_hset {n} {A} `{IsHSet A}
  : IsTrunc n.+3 A
  := (@trunc_leq 0 n.+3 tt _ _).
 *)

(** Consider the preceding definitions as instances for typeclass search, 
but only if the requisite hypothesis is already a known assumption; 
otherwise they result in long or interminable searches. *)
(*
#[export]
Hint Immediate trunc_contr : typeclass_instances.
#[export]
Hint Immediate trunc_hprop : typeclass_instances.
#[export]
Hint Immediate trunc_hset : typeclass_instances.
*)


(** From https://github.com/HoTT/HoTT/blob/master/theories/Basics/Trunc.v *)

(** Equivalence preserves truncation (this is, of course, trivial with univalence).
   This is not an [Instance] because it causes infinite loops.
   
Definition trunc_equiv A {B} (f : A -> B)
  `{IsTrunc n A} `{IsEquiv A B f}
  : IsTrunc n B. *)

(* Type class search would try to prove  IsTrunc n B
by finding A f such that IsEquiv A B f.
It would find B, idmap and produce IsTrunc n B as the new goal. *)


(** https://github.com/HoTT/HoTT/blob/master/theories/Truncations/Core.v 

Trunc n is defined as a Higher Inductive Type.
We will see what this is later in Egbert's lecture. *)

(* Truncated logic from day1. Under this interpretation, 
   the rules of intuitionistic first order logic are derivable.
   Try! 

Definition merely (A : Type@{i}) : HProp@{i} := Build_HProp (Tr (-1) A).

Definition hexists {X} (P : X -> Type) : HProp := merely (sig P).

Definition hor (P Q : Type) : HProp := merely (P + Q).

Notation "A \/ B" := (hor A B) : type_scope. *)


(** Function extensionality  *)

(* https://github.com/HoTT/HoTT/blob/master/theories/Metatheory/FunextVarieties.v 
   From day 1. *)
Definition NaiveFunext :=
  forall (A : Type@{i}) (P : A -> Type@{j}) (f g : forall x, P x),
    (forall x, f x = g x) -> (f = g).
Check NaiveFunext@{i j max}.   (* We can have these axioms at many universe levels *)

(* The proof that univalence implies function extensionality.

https://github.com/HoTT/HoTT/blob/master/theories/Metatheory/UnivalenceImpliesFunext.v *)

(* Several different formulations of univalence are equivalent.  
https://github.com/HoTT/HoTT/blob/master/theories/Metatheory/UnivalenceVarieties.v
*)

(** Now we've located most of the material from day1, you should be able to do the exercises.
    Note: The Metatheory directory contains some advanced proofs.
 *)


(*** Higher-inductive types in Coq. *)
(** Higher inductive types are inductive types where one also adds constructors for paths *)
(** This allows us to develop synthetic homotopy (Egbert's lecture).
    We only give some very basic examples. *)

(** The interval is the type with two endpoints (0,1) and a path between them.
    We would like to define it like so:
Higher Inductive interval : Type0 :=
  | zero : interval
  | one : interval
  | seg : zero = one.

But Coq does not support support this. (cubical now does!) 
So, we use Licata's trick.
https://homotopytypetheory.org/2011/04/23/running-circles-around-in-your-proof-assistant/ 

Uses Private Inductive types in Coq. Disables pattern matching/discrimate tactic.
This is used in the definition of the interval to avoid defining the booleans.
The insight is that this definition reduces on points (but not on paths).
interval_rec a b _ zero = a  (judgementally ! )

https://github.com/HoTT/HoTT/blob/master/theories/HIT/Interval.v

The h-coequalizers are other examples:
https://github.com/HoTT/HoTT/blob/master/theories/HIT/Coeq.v
and the Circle defined as a Coeq.
https://github.com/HoTT/HoTT/blob/master/theories/Spaces/Circle.v
*)
