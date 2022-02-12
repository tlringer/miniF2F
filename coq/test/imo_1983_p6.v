(*
 * Author: Jason Chen
 * setting up a bit of infrastructure for "inequalities with triangles"
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

Definition triangle a b c : Prop :=
  0 < a /\ 0 < b /\ 0 < c /\
  a < b + c /\ b < c + a /\ c < a + b.

(*
 * proof taken from
 * https://artofproblemsolving.com/wiki/index.php/1983_IMO_Problems/Problem_6
 *)

Lemma ravi : forall a b c,
  triangle a b c ->
  exists x y z,
  0 < x /\
  0 < y /\
  0 < z /\
  a = y + z /\
  b = z + x /\
  c = x + y.
Proof.
  intros.
  unfold triangle in H.
  exists ((b + c - a) / 2).
  exists ((c + a - b) / 2).
  exists ((a + b - c) / 2).
  repeat split.
  4, 5, 6: lra.
  all: match goal with
  | H : _ |- _ < ?x / _ => enough (0 < x) by lra; lra
  end.
Qed.



Lemma quadratic_no_roots_discriminant_lt_0 :
  forall a b c : R,
    (forall x, a * x² + b * x + c >= 0) ->
    b ^ 2 - 4 * a * c <= 0.
Proof.
  intros.
  unfold Rsqr in H.
  induction (Req_EM_T a 0%R).
  - subst.
    ring_simplify.
    enough (b = 0%R). subst. lra.
    setoid_rewrite Rmult_0_l in H.
    setoid_rewrite Rplus_0_l in H.
    induction (Rlt_or_le c 0%R).
    specialize H with (x := 0%R); lra.
    induction (Req_EM_T b 0%R); try lra.
    exfalso.
    induction (Rle_lt_or_eq_dec 0%R c H0); clear H0.
    * specialize H with (x := - 2 * c / b).
      field_simplify in H; lra.
    * specialize H with (x := 0 - / b).
      field_simplify in H; lra.
  - induction (Rle_or_lt a 0%R).
    * (* a < 0 case impossible *)
      assert (a < 0) by lra. clear b0 H0.
      exfalso.
      induction (Rle_or_lt 0%R (b ^ 2 - 4 * a * c)).
      + (* if has roots, compute a contradiction *)
        specialize H with (x := (- b + sqrt (b * b - 4 * a * (c + 1))) / (2 * a)).
        field_simplify in H; try lra.
        rewrite pow2_sqrt in H; try lra.
        field_simplify in H; try lra.
        field_simplify in H; try lra.
      + specialize H with (x := -b / (2 * a)).
        field_simplify in H; try lra.
        apply Rge_le in H.
        apply Ropp_lt_contravar in H0.
        ring_simplify in H0. rewrite Rplus_comm in H0. ring_simplify in H0.
        assert (0 < -(4 * a)) by lra.
        pose proof (Rdiv_lt_0_compat _ _ H0 H2).
        rewrite Ropp_div_den in H3.
        lra. lra.
    * specialize H with (x := - b / (2 * a)).
      field_simplify in H; try lra.
      assert (4 * a >= 0) by lra.
      pose proof (Rmult_ge_compat_r (4 * a) _ _ H1 H).
      field_simplify in H2; lra.
Qed.


Lemma cauchy_schwarz3 : forall a1 a2 a3 b1 b2 b3,
  (a1 * b1 + a2 * b2 + a3 * b3) ^ 2 <=
    (a1 ^ 2 + a2 ^ 2 + a3 ^ 2) * (b1 ^ 2 + b2 ^ 2 + b3 ^ 2).
Proof.
  intros.

  remember (a1 ^ 2 + a2 ^ 2 + a3 ^ 2) as A.
  remember (b1 ^ 2 + b2 ^ 2 + b3 ^ 2) as B.
  remember (a1 * b1 + a2 * b2 + a3 * b3) as D.
  
  enough ((2 * D) ^ 2 - 4 * A * B <= 0) by lra.
  eapply quadratic_no_roots_discriminant_lt_0.
  intro.

  subst.

  unfold Rsqr.
  enough ((a1 * x + b1) ^ 2 + (a2 * x + b2) ^ 2 + (a3 * x + b3) ^ 2 >= 0) by lra.

  pose proof (Rle_0_sqr (a1 * x + b1)).
  pose proof (Rle_0_sqr (a2 * x + b2)).
  pose proof (Rle_0_sqr (a3 * x + b3)).
  unfold Rsqr in *.
  lra.
Qed.

Theorem imo_1983_p6:
  forall (a b c : R),
  triangle a b c ->
  a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a) >= 0.
Proof.
  intros.

  (* use Ravi substitution and rewrite *)
  pose proof (ravi a b c H).
  (* is there a better way to do this? *)
  destruct H0 as (x, H0).
  destruct H0 as (y, H0).
  destruct H0 as (z, H0).
  destruct H0 as (?, H0).
  destruct H0 as (?, H0).
  destruct H0 as (?, H0).
  destruct H0 as (?, H0).
  destruct H0 as (?, H0).
  rewrite H0, H4, H5.

  enough ((x * y ^ 3 + y * z ^ 3 + z * x ^ 3) >= (x * y * z) * (x + y + z)) by lra.

  pose proof (cauchy_schwarz3 (sqrt (x * y ^ 3))
                              (sqrt (y * z ^ 3))
                              (sqrt (z * x ^ 3))
                              (sqrt z) (sqrt x) (sqrt y)).

  assert (0 <= x) by lra.
  assert (0 <= y) by lra.
  assert (0 <= z) by lra.

  do 3 rewrite pow2_sqrt in H6;
       try eapply Rmult_le_pos; try assumption;
       try eapply pow_le; try assumption.
  do 3 rewrite pow2_sqrt in H6; try assumption.

  do 3 rewrite sqrt_mult_alt in H6; try assumption.

  replace (x ^ 3)%R with (x * x ^ 2) in H6 at 1 by lra.
  replace (y ^ 3)%R with (y * y ^ 2) in H6 at 1 by lra.
  replace (z ^ 3)%R with (z * z ^ 2) in H6 at 1 by lra.
  do 3 rewrite sqrt_mult_alt in H6; try assumption.
  do 3 rewrite sqrt_pow2 in H6; try assumption.
  
  assert ((sqrt x * sqrt y * sqrt z) ^ 2 * (x + y + z) ^ 2 <=
          (x * y ^ 3 + y * z ^ 3 + z * x ^ 3) * (z + x + y)) by lra.
  clear H6.
  replace ((sqrt x * sqrt y * sqrt z) ^ 2)%R with
          (sqrt x ^ 2 * sqrt y ^ 2 * sqrt z ^ 2) in H10 by lra.
  do 3 rewrite pow2_sqrt in H10; try assumption.
  
  assert (0 < x + y + z) by lra.
  apply Rinv_0_lt_compat in H6.
  apply Rlt_le in H6.

  apply (Rmult_le_compat_r _ _ _ H6) in H10.
  replace (z + x + y) with (x + y + z) in H10 by lra.
  field_simplify in H10; try lra.
Qed.
