(*
 * Author: Jason Chen
 *)

Require Import Reals Lra Lia.

Infix "+" := Rplus.
Infix "-" := Rminus.
Infix "*" := Rmult.
Infix "/" := Rdiv.

Infix "<" := Rlt.
Infix "<=" := Rle.
Infix ">=" := Rge.
Infix ">" := Rgt.

Lemma cos_times_sin :
  forall x y : R,
  cos x * sin y = (sin (x + y) - sin (x - y)) / 2.
Proof.
  intros.
  pose proof (sin_plus x y).
  pose proof (Rplus_eq_compat_r (- sin (x - y)) _ _ H).
  rewrite (sin_minus x y) in H0 at 2.
  lra.
Qed.

Theorem imo_1983_p5 :
  cos (PI / 7) - cos (2 * PI / 7) + cos (3 * PI / 7) = 1 / 2.
Proof.
  remember (PI / 7) as t.
  replace (2 * PI / 7) with (2 * t) by lra.
  replace (3 * PI / 7) with (3 * t) by lra.
  apply (Rmult_eq_reg_r (sin t)).
  rewrite Rmult_plus_distr_r.
  rewrite Rmult_minus_distr_r.
  rewrite cos_times_sin.
  rewrite cos_times_sin.
  rewrite cos_times_sin.

  replace (t + t) with (2 * t) by lra.
  replace (t - t) with 0%R by lra.
  replace (2 * t + t) with (3 * t) by lra.
  replace (2 * t - t) with t by lra.
  replace (3 * t + t) with (4 * t) by lra.
  replace (3 * t - t) with (2 * t) by lra.

  field_simplify.
  rewrite sin_0.
  rewrite <- sin_PI_x.
  replace (PI - 3 * t) with (4 * t) by lra.
  field_simplify.
  reflexivity.

  subst.
  enough (0 < sin (PI / 7)) by lra.
  apply sin_gt_0; pose proof PI_RGT_0; lra.
Qed.
  
