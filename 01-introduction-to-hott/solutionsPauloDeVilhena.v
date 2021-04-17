From HoTT Require Import HoTT.

(* Solution of exercise 5.2. *)

(* Compiles with Coq 8.13.1 and Coq-HoTT 8.13. *)

Section Part_5_Univalence.

  Section Exercise_5_2.

    (* Show that Σ (A : U) . isSet A is not a set. Hint: (2 ≃ 2) ≃ 2. *)

    Definition hset' : Type := { A : Type & IsHSet A }.

    Definition Bool' : hset' := (Bool : Type; hset_bool).

    Definition two_equiv_two `{UA : Univalence} : Bool <~> (Bool' = Bool').
    Proof.
      apply transitive_equiv with (y := (Bool <~> Bool)).
      - apply equiv_bool_aut_bool.
      - apply transitive_equiv with (y := (Bool = Bool)).
        + apply (equiv_path_universe Bool Bool).
        + apply transitive_equiv with (y := (Bool'.1 = Bool'.1)); [reflexivity|].
          apply equiv_path_sigma_hprop.
    Defined.

    Lemma set_not_set `{UA : Univalence} : IsHSet hset' -> Empty.
    Proof.
      intro HS. destruct two_equiv_two as [f [g _ gf_idmap _]].
      cut (true = false).
      - inversion 1.
      - transitivity (g (f true)).
        + symmetry. apply gf_idmap.
        + transitivity (g (f false)).
          * apply ap. apply hset_path2.
          * apply gf_idmap.
    Qed.

  End Exercise_5_2.

End Part_5_Univalence.
