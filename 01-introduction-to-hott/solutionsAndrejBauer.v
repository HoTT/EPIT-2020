From HoTT Require Import HoTT.

(* This file formalizes the exercises from the lectures "Introduction to HoTT". *)

Section Part_1_Martin_Lof_Type_Theory.

  Section Exercise_1_1.

    (* Construct an element of

       (Π (x:A) . Σ (y:B) . C x y) → Σ (f : A → B) . Π (x : A) . C x (f x).
    *)

    Definition Exercise_1_1 (A : Type) (B : Type) (C : A -> B -> Type) :
             (forall x, { y : B & C x y}) -> { f : A -> B         &  forall x,   C x (f x) }
    :=   fun f                            => ( fun x => (f x).1   ;  fun    x => (f x).2   ).

  End Exercise_1_1.


  Section Exercise_1_2.

    (* Use ind_ℕ to define double : ℕ → ℕ which doubles a number. *)

    Definition double : nat -> nat :=
      nat_rec _ O (fun _ k => S (S k)).

  End Exercise_1_2.

  Section Exercise_1_3.

    (* Define halve : ℕ → ℕ which halves a number (rounded down). *)

    Definition halve_helper : (nat -> nat * Bool)%type.
    Proof.
      intro n ; induction n as [|n [k b]].
      - exact (O, true).
      - exact ((if b then k else S k), negb b).
    Defined.

    Definition halve : nat -> nat := fst o halve_helper.

  End Exercise_1_3.

End Part_1_Martin_Lof_Type_Theory.

Section Part_2_Identity_Types.

  Section Exercise_2_1.

    (* Construct a path between paths: p · idpath = p. *)

    Theorem Exercise_2_1 (A : Type) (x y : A) (p : x = y) : p @ idpath y = p.
    Proof.
      induction p.
      reflexivity.
    Defined.

  End Exercise_2_1.

  Section Exercise_2_2.

    (* Given a path p : x = y construct p⁻¹ : y = x and show that idpath⁻¹ = idpath. *)

    Definition inv {A : Type} {x y : A} : x = y -> y = x.
    Proof.
      intro p ; induction p.
      exact idpath.
    Defined.

    Definition inv' {A : Type} {x y : A} : x = y -> y = x.
    Proof.
      now intros [].
    Defined.

    Definition inv'' {A : Type} {x y : A} (p : x = y) : y = x :=
      match p with
        | idpath => idpath
      end.

    Definition inv_idpath {A : Type} {x : A} : inv (idpath x) = (idpath x).
    Proof.
      reflexivity.
    Defined.

  End Exercise_2_2.

  Section Exercise_2_3.

    (* Suppose

         u, v : Σ (x : A) . B(x)
         p : π₁ u = π₁ v
         q : p . (π₂ u) = π₂ v

       are given. Construct a path u = v. *)

    Theorem squirrel {A : Type} {B : A -> Type} :
      forall (x y : A) (p : x = y), forall (u : B x) (v : B y) (q : p # u = v), (x ; u) = (y ; v).
    Proof.
      intros x y p.
      induction p.
      intros u v q.
      induction q.
      reflexivity.
    Defined.

    Theorem Exercise_2_3
              {A : Type} {B : A -> Type}
              {u v : {x : A & B x}}
              (p : u.1 = v.1)
              (q : p # u.2 = v.2)
              : u = v.
    Proof.
      transitivity (u.1 ; u.2).
      - reflexivity.
      - transitivity (v.1 ; v.2).
        + now srapply squirrel.
        + reflexivity.
    Defined.

    Theorem Exercise_2_3'
              {A : Type} {B : A -> Type}
              {u v : {x : A & B x}}
              (p : u.1 = v.1)
              (q : p # u.2 = v.2)
              : u = v.
    Proof.
      now srapply path_sigma.
    Defined.

  End Exercise_2_3.

End Part_2_Identity_Types.

Section Part_3_Homotopy_Levels.

  Section Exercise_3_1.

    (* Construct a point if isContr A → Π (x y : A) . isContr (x = y) *)

    Theorem Exercise_3_1 (A : Type) :
      Contr A -> forall (x y : A), Contr (x = y).
    Proof.
      intros [a h] x y.
      exists ((h x)^ @ (h y)).
      intro p.
      induction p.
      apply concat_Vp.
    Defined.

    Theorem Exercise_3_1' (A : Type) :
      Contr A -> forall (x y : A), Contr (x = y).
    Proof.
      apply @istrunc_succ.
    Defined.

  End Exercise_3_1.

  Section Exercise_3_2.

    (* Is contractibility a property or a structure? *)

    Theorem Exercise_3_2 `{F : Funext} (A : Type) : IsHProp (Contr A).
    Proof.
      apply hprop_allpath.
      intros [a h] [b g].
      destruct (h b).
      apply ap.
      apply path_forall.
      intro x.
      srapply path_contr.
      apply Exercise_3_1.
      now exists a.
    Defined.

    Theorem Exercise_3_2' `{F : Funext} (A : Type) : IsHProp (Contr A).
    Proof.
      apply ishprop_istrunc.
    Defined.

  End Exercise_3_2.

  Section Exercise_3_3.

    (* Π (x : A) . isContr (Σ (y : A) . x = y *)

    Theorem Exercise_3_3 (A : Type) :
      forall (x : A), Contr ({ y : A & x = y}).
    Proof.
      intro x.
      exists (x ; idpath).
      intros [y p].
      induction p.
      reflexivity.
    Defined.

  End Exercise_3_3.

End Part_3_Homotopy_Levels.

Section Part_4_Equivalences.

  Section Exercise_4_1.

    (* (a) If P and Q are propostions then (P → Q) × (Q → P) → P ≃ Q *)

    Variables P Q : HProp.

    Context `{FE : Funext}.

    Definition cow : (P -> Q) * (Q -> P) -> P <~> Q.
    Proof.
      intros [f g].
      exists f.
      apply isequiv_biinv.
      split ; exists g ; intro x ; [ apply P | apply Q ].
    Defined.

    (* (b) The map above is an equivalence. *)

    Definition moo : IsEquiv cow.
    Proof.
      apply isequiv_biinv.
      split.
      - now exists (fun (e : P <~> Q) => (equiv_fun e , e ^-1)).
      - exists (fun (e : P <~> Q) => (equiv_fun e , e ^-1)).
        intro e.
        now apply @path_equiv.
    Defined.


    (* (c) If X and Y are sets then (X ≃ Y) ≃ (X ≅ Y). *)

    (* The library does not seem to have an explicit definition of isIso,
       so we include it here. *)

    Definition isIso {A B} (f : A -> B) : Type :=
      { g : B -> A & (g o f == idmap) * (f o g == idmap) }%type.

    Definition Iso X Y := {f : X -> Y & isIso f}.

    Definition equiv2iso {A B} : Equiv A B -> Iso A B.
    Proof.
      intro e.
      exists e, (e ^-1).
      split.
      - apply eissect.
      - apply eisretr.
    Defined.

    Theorem rabbit (X Y : HSet) : Equiv X Y <~> Iso X Y.
    Proof.
      srapply equiv_adjointify.
      - intro e.
        exists e, (e ^-1).
        split.
        + apply eissect.
        + apply eisretr.
      - intros [f [g [gf_idmap fg_idmap]]].
        exists f.
        apply isequiv_biinv.
        split ; now exists g.
      - intros [f [g [gf_idmap fg_idmap]]].
        srapply path_sigma ; try reflexivity.
        srapply path_sigma ; try reflexivity.
        srapply path_prod.
        + apply path_forall. intro. apply hset_path2.
        + apply path_forall. intro. apply hset_path2.
      - intro e.
        now apply path_equiv.
    Defined.

  End Exercise_4_1.

  Section Exercise_4_2.

    (* Use equivalence to express the fact that | |₋₁ : A → ∣|A||₋₁ is the
       universal map from A to proposition. *)

    (* Please formalize as follows:

       Given a map q : A → Q, define a map e such that IsEquiv e expresses
       the fact that q : A → Q is the propositional truncation of A.
    *)
    Definition isPropTruncation {A Q : Type} (q : A -> Q) :=
      forall (P : HProp), IsEquiv (fun (f : Q -> P) => f o q).

  End Exercise_4_2.

End Part_4_Equivalences.

Section Part_5_Univalence.

  Section Exercise_5_1.

    (* Show that the type of true propositions is contractible. *)

    Context `{UA : Univalence}.

    Theorem weasel : Contr { A : Type & IsHProp A * A }%type.
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
