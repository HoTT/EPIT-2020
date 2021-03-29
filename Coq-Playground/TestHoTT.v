From HoTT Require Import HoTT.

Check Contr.
Print Contr.

Goal forall x : nat, Contr (x = x).
Proof.
  intros x. exists idpath.
Abort.

Print isequiv_equiv_path.
