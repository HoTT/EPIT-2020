From HoTT Require Import HoTT.

(* This file formalizes the exercises from the lectures "Introduction to HoTT". *)

Section Part_1_Martin_Lof_Type_Theory.

  Section Exercise_1_1.

    (* Construct an element of

       (Π (x:A) . Σ (y:B) . C x y) → Σ (f : A → B) . Π (x : A) . C x (f x).
    *)

    Theorem Exercise_1_1 (A : Type) (B : Type) (C : A -> B -> Type) :
      (forall x, { y : B & C x y}) -> { f: A -> B & forall x, C x (f x) }.
    Admitted.

  End Exercise_1_1.


  Section Exercise_1_2.

    (* Use ind_ℕ to define double : ℕ → ℕ which doubles a number. *)

    Definition double : nat -> nat.
    Proof.
      (* You should use nat_rect. *)
    Admitted.

  End Exercise_1_2.

  Section Exercise_1_3.

    (* Define halve : ℕ → ℕ which halves a number (rounded down). *)
    Definition halve : nat -> nat.
    Proof.
    Admitted.

  End Exercise_1_3.

End Part_1_Martin_Lof_Type_Theory.

Section Part_2_Identity_Types.

  Section Exercise_2_1.

    (* Construct a path between paths: p · idpath = p. *)

    Theorem Exercise_2_1 (A : Type) (x y : A) (p : x = y) : p @ idpath y = p.
    Proof.
    Admitted.

  End Exercise_2_1.

  Section Exercise_2_2.

    (* Given a path p : x = y construct p⁻¹ : y = x and show that idpath⁻¹ = idpath. *)

    Definition inv {A : Type} {x y : A} : x = y -> y = x.
    Proof.
    Admitted.

    Definition inv_idpath {A : Type} {x : A} : inv (idpath x) = (idpath x).
    Proof.
    Admitted.

  End Exercise_2_2.

  Section Exercise_2_3.

    (* Suppose

         u, v : Σ (x : A) . B(x)
         p : π₁ u = π₁ v
         q : p . (π₂ u) = π₂ v

       are given. Construct a path u = v. *)
    Theorem Exercise_2_3
              {A : Type} {B : A -> Type}
              {u v : {x : A & B x}}
              (p : u.1 = v.1)
              (q : p # u.2 = v.2)
              : u = v.
    Proof.
    Admitted.

  End Exercise_2_3.

End Part_2_Identity_Types.

Section Part_3_Homotopy_Levels.

  Section Exercise_3_1.

    (* Construct a point if isContr A → Π (x y : A) . isContr (x = y) *)

    Theorem Exercise_3_1 (A : Type) :
      Contr A -> forall (x y : A), Contr (x = y).
    Proof.
    Admitted.

  End Exercise_3_1.

  Section Exercise_3_2.

    (* Is contractibility a property or a structure? *)

    (* Please formalize, use "Contr", "IsHProp". *)

  End Exercise_3_2.

  Section Exercise_3_3.

    (* Π (x : A) . isContr (Σ (y : A) . x = y *)

    (* Please formalize. *)

  End Exercise_3_3.

End Part_3_Homotopy_Levels.

Section Part_4_Equivalences.

  Section Exercise_4_1.

    (* (a) If P and Q are propostions then (P → Q) × (Q → P) → P ≃ Q *)

    Variables P Q : HProp.

    Definition cow : (P -> Q) * (Q -> P) -> P <~> Q.
    Proof.
    Admitted.

    (* (b) The map above is an equivalence. *)

    Definition moo : IsEquiv cow.
    Proof.
    Admitted.

    (* (c) If X and Y are sets then (X ≃ Y) ≃ (X ≅ Y). *)

    (* The library does not seem to have an explicit definition of isIso,
       so we include it here. *)

     Definition isIso {A B} (f : A -> B) : Type :=
      { g : B -> A & (g o f == idmap) * (f o g == idmap) }%type.

    Theorem rabbit (X Y : HSet) : (X <~> Y) <~> { f : X -> Y & isIso f }.
    Proof.
    Admitted.

  End Exercise_4_1.

  Section Exercise_4_2.

    (* Use equivalence to express the fact that | |₋₁ : A → ∣|A||₋₁ is the
       universal map from A to proposition. *)

    (* Please formalize as follows:

       Given a map q : A → Q, define a map e such that IsEquiv e expresses
       the fact that q : A → Q is the propositional truncation of A.
    *)

  End Exercise_4_2.

End Part_4_Equivalences.

Section Part_5_Univalence.

  Section Exercise_5_1.

    (* Show that the type of true propositions is contractible. *)

    Theorem weasel : Contr { A : HProp & A }.
    Proof.
    Admitted.

  End Exercise_5_1.

  Section Exercise_5_2.

    (* Show that Σ (A : U) . isSet A is not a set. Hint: (2 ≃ 2) ≃ 2. *)

    Lemma two_equiv_two : (Bool <~> Bool) <~> Bool.
    Proof.
    Admitted.

    Lemma set_not_set : IsHSet HSet -> Empty.
    Proof.
    Admitted.

  End Exercise_5_2.

End Part_5_Univalence.
