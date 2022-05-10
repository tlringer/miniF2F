(*
 * Author: Max Fan 
 *)
Require Import Reals Lra Lia.
Infix "/" := Rdiv.
Infix "+" := Rplus.
Infix "*" := Rmult.
Infix "-" := Rminus.

Theorem amc_12_2000_p11 :
  forall (a b : R), (a <> 0%R /\ b <> 0%R) ->
    (a * b = a - b) ->
    (a / b + b / a - a * b = 2%R).
Proof.
  intros.
  destruct H.
  field_simplify_eq; auto.
  replace (- a ^ 2 * b ^ 2) with ((a * b) * (a * b)* -1) by lra.
  rewrite H0.
  field_simplify_eq.
  auto.
Qed.