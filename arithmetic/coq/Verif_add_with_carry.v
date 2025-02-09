Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.

Require Import Didactica.arithmetic.
Require Import Didactica.Add.
Require Import Didactica.number.

Lemma overflowing_add : forall a b : Z,
  digit_bound a ->
  digit_bound b ->
  (and
    (digit_bound (Z.modulo
      (Z.add a b)
      Int64.modulus))
    (eq
      (Int64.repr (Z.add a b))
      (Int64.repr (Z.modulo
        (Z.add a b)
        Int64.modulus)))).
Proof.
  intros. split.
  - unfold digit_bound in *.
    assert
      (0 <= (a + b) mod Int64.modulus < Int64.modulus)
    by apply
      (Z.mod_pos_bound
        (a + b)
        Int64.modulus
        ltac:(rep_lia)).
    unfold base_bound.
    rep_lia.
  - apply Int64.eqm_samerepr. unfold Int64.eqm.
    unfold Zbits.eqmod. exists ((a + b)/Int64.modulus).
    rewrite (Z.mul_comm ((a + b)/Int64.modulus) Int64.modulus).
    apply Z_div_mod_eq_full.
Qed.

Lemma ltu_translation : forall a b,
  digit_bound a ->
  digit_bound b ->
  (eq 
    (Int64.ltu
      (Int64.repr a)
      (Int64.repr b))
    (Z.ltb a b)).
Proof.
  intros a b bound_a bound_b.
  unfold digit_bound, base_bound in *.
  destruct
    (Int64.ltu (Int64.repr a) (Int64.repr b))
  eqn:comparison.
  - apply
      (ltu_inv64 (Int64.repr a) (Int64.repr b))
    in comparison. normalize in comparison. lia.
  - apply
      (ltu_false_inv64 (Int64.repr a) (Int64.repr b))
    in comparison. normalize in comparison. lia.
Qed.

Lemma body_add_with_carry :
  (semax_body Vprog Gprog f_add_with_carry add_with_carry_spec).
Proof.
  start_function.
  generalize
    (add_back_to_bool
      Int64.modulus
      carry_in
      left_digit
      right_digit
      ltac:(rep_lia)
      ltac:(unfold digit_bound, base_bound in *; lia)
      ltac:(unfold digit_bound, base_bound in *; lia));
  intros back_to_bool; simpl in back_to_bool.
  forward. deadvars!. normalize.
  generalize
    (bool_bound carry_in);
  intros carry_bound.
  generalize
    (overflowing_add
      (Z.b2z carry_in)
      left_digit
      ltac:(unfold digit_bound, base_bound; rep_lia)
      H);
  intros [temporary_bound overflowed];
  rewrite overflowed; clear overflowed.
  remember
    ((Z.b2z carry_in + left_digit) mod Int64.modulus)
  as temporary.
  forward. normalize.
  generalize
    (overflowing_add
      temporary
      right_digit
      temporary_bound
      H0);
  intros [result_bound overflowed];
  rewrite overflowed; clear overflowed.
  remember
    ((temporary + right_digit) mod Int64.modulus)
  as result.
  forward. normalize.
  rewrite
    (ltu_translation
      temporary
      (Z.b2z carry_in)
      temporary_bound
      ltac:(unfold digit_bound, base_bound; rep_lia)).
  rewrite
    (ltu_translation
      result
      right_digit
      result_bound
      H0).
  generalize
    (bool_bound (Z.ltb temporary (Z.b2z carry_in)));
  intros left_overflow_bound.
  generalize
    (bool_bound (Z.ltb result right_digit));
  intros right_overflow_bound.
  normalize.
  rewrite back_to_bool.
  forward.
Qed.
