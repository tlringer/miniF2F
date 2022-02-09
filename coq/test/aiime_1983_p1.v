(*
 * Author: Talia Ringer
 *
 * Real numbers are terrible in Coq, and I don't know why lra is so brittle,
 * so this can probably be improved a lot, but whatever.
 *)
Require Import Reals Lra.
Infix "/" := Rdiv.
Infix "+" := Rplus.
Infix "*" := Rmult.
Infix "-" := Rminus.

(*
 * Lift ln to nats
 *)
Definition ln (n : nat) : R :=
  ln (INR n).

(*
 * Lift ln lemmas to nats
 *)
Lemma ln_mult :
  forall x y : nat,
    0 < x ->
    0 < y ->
    ln (x * y) = ln x + ln y.
Proof.
  intros. unfold ln. rewrite mult_INR. apply ln_mult; auto using lt_0_INR.
Qed.

Ltac multiply_both_sides x H :=
  apply (f_equal (Rmult x)) in H;
  rewrite <- Rmult_assoc in H;
  try rewrite Rinv_r_simpl_m in H;
  auto.

Ltac by_lra x y :=
  replace x with y by lra.

Ltac by_lra_in x y H :=
  replace x with y in H by lra.

Ltac by_ln_mult_in H :=
  rewrite ln_mult in H; try apply Nat.mul_pos_pos; auto with arith.

Lemma lt_ln_neq :
  forall x,
    1 < x ->
    ln x <> 0%R.
Proof.
  intros. apply ln_neq_0.
  - unfold not. intros. replace 1%R with (INR 1) in H0 by reflexivity.
    pose proof (INR_eq _ _ H0). subst. inversion H. inversion H2.
  - replace 0%R with (INR 0) by reflexivity. apply lt_INR. auto with arith.
Qed.

(*
 * The problem, a gross sequence of rewrites
 *)
Theorem aime_1983_p1:
  forall (x y z w : nat),
    1 < x /\ 1 < y /\ 1 < z ->
    0 <= w ->
    ln w / ln x = 24%R ->
    ln w / ln y = 40%R ->
    ln w / ln (x * y * z) = 12%R ->
    ln w / ln z = 60%R.
Proof.
  intros. unfold Rdiv in *.
  destruct H. destruct H4.
  pose proof (lt_ln_neq _ H). pose proof (lt_ln_neq _ H4). pose proof (lt_ln_neq _ H5).
  assert (1 < x * y * z) by (repeat (apply Nat.lt_1_mul_pos; auto with arith)).
  pose proof (lt_ln_neq _ H9).
  repeat by_ln_mult_in H3.
  repeat by_ln_mult_in H10.
  multiply_both_sides (ln x) H1.
  multiply_both_sides (ln y) H2.
  multiply_both_sides (ln x + ln y + ln z) H3.
  rewrite H1 in H2. 
  by_lra_in (ln x * 24) (8 * (ln x * 3)) H2.
  by_lra_in (ln y * 40) (8 * (ln y * 5)) H2.
  multiply_both_sides (Rinv 8) H2.
  by_lra_in (((/ 8) * 8) * ((ln x) * 3)) (ln x * 3) H2.
  by_lra_in (/ 8 * (8 * (ln y * 5))) (ln y * 5) H2.
  multiply_both_sides (Rinv 3) H2.
  by_lra_in (((/ 3) * (ln x)) * 3) (ln x) H2.
  by_lra_in (/ 3 * (ln y * 5)) ((5 / 3) * (ln y)) H2.
  rewrite H2 in H3. 
  by_lra_in ((5 / 3 * ln y + ln y + ln z) * 12) (32 * ln y + 12 * ln z) H3.
  rewrite H1. rewrite H2. rewrite H1 in H3. rewrite H2 in H3.
  apply (f_equal (fun x => x - (32 * ln y))) in H3.
  by_lra_in (32 * ln y + 12 * ln z - 32 * ln y) (12 * ln z) H3.
  by_lra_in (5 / 3 * ln y * 24 - 32 * ln y) (8 * ln y) H3.
  by_lra (5 / 3 * ln y * 24 * / ln z) (5 * (8 * ln y) / ln z).
  rewrite H3. rewrite <- Rmult_assoc. by_lra 60%R (60 * 1). by_lra (5 * 12) (60%R).
  unfold Rdiv. rewrite Rmult_assoc.
  f_equal; try lra. rewrite Rinv_r_sym with (r := ln z); auto.
Qed.
