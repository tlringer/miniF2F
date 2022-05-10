(*
 * Author: Max Fan 
 *)
Require Import Lia.


Lemma sfft_factor :
  forall (x y : nat),
    (0 < y) ->
    (y < x) ->
    (x + y + (x * y) = 80) -> ((x + 1) * (y+1) = 81).
Proof.
  intros.
  lia.
Qed.

Theorem amc12a_2015_p10 :
  forall (x y : nat),
    (0 < y) ->
    (y < x) ->
    (x + y + (x * y) = 80) ->
    x = 26.
Proof.
  intros.
  specialize (sfft_factor x y).
  intros.
  auto.
  pose proof (((H2 H) H0) H1).
  (* needs to reason about factorizations of 81, very doable *)
  give_up.
Admitted.
