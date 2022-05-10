(*
 * Author: Max Fan 
 *)
Require Import Reals Lra Lia.
Infix "/" := Rdiv.
Infix "+" := Rplus.
Infix "*" := Rmult.
Infix "-" := Rminus.

Lemma constructive_example : ((1%R <> 0%R /\ 0.5%R <> 0%R) ->
    (1%R * 0.5%R = 1%R - 0.5%R) ->
    (1%R / 0.5%R + 0.5%R / 1%R - 1%R * 0.5%R = 2%R)).
Proof.
  intros.
  lra.
Qed.

Theorem amc_12_2000_p11 :
  exists (a b : R), (a <> 0%R /\ b <> 0%R) ->
    (a * b = a - b) ->
    (a / b + b / a - a * b = 2%R).
Proof.
  eapply ex_intro.
  eapply ex_intro.
  apply constructive_example.
Qed.