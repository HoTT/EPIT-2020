(* If loading this file in emacs, remove first the last few lines that force to call `hoqtop` and rather use the `_CoqProject` method described in the installation instructions *)

From HoTT Require Import HoTT.

(* This file formalizes the exercises from the lectures "Introduction to HoTT". *)

Section Part_1_Martin_Lof_Type_Theory.

  Section Exercise_1_1.

    (* Construct an element of

       (Π (x:A) . Σ (y:B) . C x y) → Σ (f : A → B) . Π (x : A) . C x (f x).
    *)

    Theorem Exercise_1_1 (A : Type) (B : Type) (C : A -> B -> Type) :
      (forall x, { y : B & C x y}) -> { f: A -> B & forall x, C x (f x) }.
    Proof.
      intros g.
      exists (fun x => (g x).1).
      intros x.
      case (g x) as [y ?].
      assumption.
    Defined.

  End Exercise_1_1.


  Section Exercise_1_2.

    (* Use ind_ℕ to define double : ℕ → ℕ which doubles a number. *)

    Definition double : nat -> nat.
    Proof.
      apply nat_rect.
      - exact 0%nat.
      - intros _ s. exact (s.+2)%nat.
      (* You should use nat_rect. *)
    Defined.

    Eval compute in (double 3).

  End Exercise_1_2.

  Section Exercise_1_3.

    (* Define halve : ℕ → ℕ which halves a number (rounded down). *)
    Definition halve : nat -> nat.
    Proof.
    assert (halve_aux : nat -> nat * Bool).
    - apply nat_rect.
      + exact (0%nat,true).
      + intros _ [h b].
        exact (if b then (h,false) else ((S h),true)).
    - intros n. exact (fst (halve_aux n)).
    Defined.

    Eval compute in (halve 17).

  End Exercise_1_3.

End Part_1_Martin_Lof_Type_Theory.

Section Part_2_Identity_Types.

  Section Exercise_2_1.

    (* Construct a path between paths: p · idpath = p. *)

    Theorem Exercise_2_1 (A : Type) (x y : A) (p : x = y) : p @ idpath y = p.
    Proof.
      case p. reflexivity.
    Defined.

  End Exercise_2_1.

  Section Exercise_2_2.

    (* Given a path p : x = y construct p⁻¹ : y = x and show that idpath⁻¹ = idpath. *)

    Definition inv {A : Type} {x y : A} : x = y -> y = x.
    Proof.
      intros []. reflexivity.
    Defined.

    Definition inv_idpath {A : Type} {x : A} : inv (idpath x) = (idpath x).
    Proof.
      reflexivity.
    Defined.

  End Exercise_2_2.

  Section Exercise_2_3.

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
    destruct u, v.
    cbn in *.
    destruct p.
    cbn in *.
    destruct q.
    reflexivity.
    Qed.

  End Exercise_2_3.

End Part_2_Identity_Types.

Section Part_3_Homotopy_Levels.

  Section Exercise_3_1.

    (* Construct a point if isContr A → Π (x y : A) . isContr (x = y) *)

    Theorem Exercise_3_1 (A : Type) :
      Contr A -> forall (x y : A), Contr (x = y).
    Proof.
        intros [a c] x y.
        exists ((c x)^@(c y)).
        intros [].
        case (c x).
        reflexivity.
    Defined.


  End Exercise_3_1.

  Section Exercise_3_2.

    (* Is contractibility a property or a structure? *)

    (* Please formalize, use "Contr", "IsHProp". *)

    Theorem Exercise_3_2 `{Funext} (A : Type) : IsHProp (Contr A).
    Proof.
        apply hprop_allpath.
        intros [x hx] [y hy].
        induction (hx y).
        apply ap.
        rapply path_contr.
        rapply contr_forall.
        apply Exercise_3_1.
        eexists.
        exact hx.
    Defined.

  End Exercise_3_2.

  Section Exercise_3_3.

    (* Π (x : A) . isContr (Σ (y : A) . x = y *)

    (* Please formalize. *)

    Theorem Exercise_3_3 (A : Type) (x : A) : Contr (exists (y : A), x = y).
    Proof.
        exists (exist _ x (idpath x)).
        intros [? []].
        reflexivity.
    Defined.

  End Exercise_3_3.

End Part_3_Homotopy_Levels.

Section Part_4_Equivalences.

  Section Exercise_4_1.

    (* (a) If P and Q are propostions then (P → Q) × (Q → P) → P ≃ Q *)

    Variables P Q : hProp.

    Definition cow : (P -> Q) * (Q -> P) -> P <~> Q.
    Proof.
        cbn in *.
        intros [f g].
        exists f.
        apply isequiv_biinv.
        split.
        all: exists g ; intro.
        - apply P.
        - apply Q.  
    Defined.

    (* (b) The map above is an equivalence. *)

    Definition moo `{Funext} : IsEquiv cow.
    Proof.
    unshelve eexists.
    + intros [f e].
      apply contr_map_isequiv in e.
      split.
      1: exact f.
      intros q.
      specialize (e q).
      destruct e as [[]].
      eassumption.
    + cbn.
      intros f.
      apply path_equiv.
      reflexivity.
    + cbn.
      intros [f g].
      apply path_prod ; cbn.
      all: reflexivity.
    + intros [f g].
      apply path_ishprop.
    Defined.

    (* (c) If X and Y are sets then (X ≃ Y) ≃ (X ≅ Y). *)

    (* The library does not seem to have an explicit definition of isIso,
       so we include it here. *)

    Definition isIso {A B} (f : A -> B) : Type :=
      { g : B -> A & (f o g == idmap) * (g o f == idmap) }%type.
  
    Theorem rabbit `{Funext} (X Y : hSet) : (X <~> Y) <~> { f : X -> Y & isIso f }.
    Proof.
    srapply equiv_adjointify.
    - intros [f [g ]].
      exists f, g.
      now split.
    - intros (f&?&[]).
      exists f.
      unshelve econstructor.
      1-3: eassumption.
      intros. apply Y.
    - cbn.
      intros (?&?&[]).
      now repeat apply ap.
    - cbn.
      intros [? []].
      repeat apply ap.
      apply path_forall.
      intro.
      apply hset_path2.
    Qed.

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

    Theorem weasel : Univalence -> Contr { A : hProp & A }.
    Proof.
        exists (Unit_hp ; tt).
        intros [A a].
        unshelve eapply path_sigma'.
        -   apply path_iff_hprop.
            + exact (fun _ => a).
            + exact (fun _ => tt).
        - apply A.
    Defined.

  End Exercise_5_1.

  Section Exercise_5_2.

    (* Show that Σ (A : U) . isSet A is not a set. Hint: (2 ≃ 2) ≃ 2. *)

    Lemma two_equiv_two `{Funext} : (Bool <~> Bool) <~> Bool.
    Proof.
    unshelve eapply equiv_adjointify.
    - intros [f _].
      exact (f true).
    - exact (fun b : Bool => if b then (equiv_idmap Bool) else equiv_negb).
    - intros [] ; reflexivity.
    - intros [f [g fg gf ?]].
      apply path_equiv.
      apply path_forall.
      intros b.
      cbn.
      remember (f true) as ft eqn:eft.
      destruct ft.
      + destruct b ; cbn.
        1: symmetry ; assumption.
        remember (f false) as ff eqn: eff.
        destruct ff.
        2: reflexivity.
        rewrite <- (gf false), <- (gf true), eft, eff.
        reflexivity.
      + destruct b ; cbn.
        1: symmetry ; assumption.
        remember (f false) as ff eqn: eff.
        destruct ff.
        1: reflexivity.
        rewrite <- (gf true), <- (gf false), eft, eff.
        reflexivity.
    Qed.

    Lemma set_not_set `{ua : Univalence} : IsHSet hSet -> Empty.
    Proof.
    intros H.
    unshelve refine (let B : hSet := _ in _ ).
    1:{ exists Bool. apply hset_bool. }
    assert (Contr (B = B)).
    1:{
      unshelve econstructor.
      1: exact idpath.
      intros y.
      apply hset_path2.
    }
    assert (Contr (Bool = Bool)).
    {
      eapply contr_equiv'.
      2: eassumption.
      symmetry.
      eapply equiv_path_trunctype'.
    }
    assert (Contr (Bool)) as [b eb].
    1:{ eapply contr_equiv'.
        2: eassumption.
        etransitivity.
        2: apply two_equiv_two.
        etransitivity.
        2: exact (equiv_equiv_path Bool Bool).
        reflexivity.
    }
    destruct b ; [specialize (eb false) | specialize (eb true)].
    all: inversion eb.
    Qed.
    
  End Exercise_5_2.

End Part_5_Univalence.
