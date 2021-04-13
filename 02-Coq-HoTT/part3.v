(*** Quotients and impredicativity, Axioms *)


(** Slides ... *)


(** Another example of a HIT is truncation, but that definition is done at a high level of modalities. *)
(** Voevodsky defined truncation impredicatively:
   Definition merely (A : Type) : Type
    := forall P:Type, IsHProp P -> (A -> P) -> P.

He proposed a variant of impredicativity where all propositions are in the lowest level,
but there is no known model for this. This is still used in the UniMath library. *)

(** Impredicativity 
    https://github.com/HoTT/HoTT/blob/master/theories/PropResizing/PropResizing.v
    For a proposition P in universe U_i, we can find an equivalent proposition in any other universe U_j.

Axiom resize_hprop : forall `{PropResizing} (A : Type@{i}) `{IsHProp A}, Type@{j}.
Axiom equiv_resize_hprop : forall `{PropResizing} (A : Type@{i}) `{IsHProp A},
    A <~> resize_hprop A.

Propositional resizing holds in many models (e.g. all Grothendieck oo-toposes). *)

(** Challenge:
   Prove that the truncation HIT is equivalent to impredicative trunction.
   https://github.com/HoTT/HoTT/blob/master/theories/PropResizing/ImpredicativeTruncation.v *)

(** Let's consider the set-quotient *)
(** https://github.com/HoTT/HoTT/blob/master/theories/HIT/quotient.v 
   (Propositional) univalence allows us show that quotients are exact. *)
(* Using impredicativity (resizing) we can construct the quotient as a collection of equivalence classes.
   The two definitions are equivalent (HoTT book), but a proof is still missing from the library.
   https://github.com/HoTT/HoTT/blob/master/theories/HIT/quotient.v#L214
   Challenge: Prove this. *)


(** After this excursion to impredicativity, we observe that quotients make hSets into an exact category.
   This is one of the important properties of an predicative topos.
   The other properties (like image factorizations) hold too.
   The theory is image factorizations is developed at the great (generality) of modalities.
   https://github.com/HoTT/HoTT/blob/master/theories/Modalities/Modality.v *)

(** Resizing makes hSets into a topos. *)

(** In HoTT we have the principle of unique choice
https://github.com/HoTT/HoTT/blob/master/theories/HIT/unique_choice.v

Lemma unique_choice {X Y} (R:X->Y->Type) :
 (forall x y, IsHProp (R x y)) -> (forall x, (hunique (R x)))
   -> {f : X -> Y & forall x, (R x (f x))}.

This is not provable if we would use Coq's Prop.
The absence of unique choice make program extraction 
from Coq to ocaml possible, as we can freely delete all proofs of propositions.
With unique choice we would need to carry those proofs around,
as they may be used later to construct other terms. *)

(* The axiom of choise is not provable, as it implies classical logic.
   Even the axiom of countable choice is not provable.
   As there are models (higher toposes) in which it does not hold.

   Christian may say more about these models. *)


(*** Axioms *)

(** UA implies funext
https://github.com/HoTT/HoTT/blob/master/STYLE.md#axioms

The interval implies funext, by currying:
https://github.com/HoTT/HoTT/blob/master/theories/Metatheory/IntervalImpliesFunext.v
(* This looks nicer in cubical *)

The truncation of the Booleans is the interval. Hence, Truncation implies Funext.
https://github.com/HoTT/HoTT/blob/master/theories/Metatheory/TruncImpliesFunext.v
*)

(** UA implies Object classifier
https://github.com/HoTT/HoTT/blob/master/theories/ObjectClassifier.v *)

(** Challenge: Prove that if the universe is an objectclassifier, then UA holds. *)
