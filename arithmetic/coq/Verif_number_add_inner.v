Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Didactica.arithmetic.
Require Import Didactica.number.

Lemma body_number_add_inner: semax_body Vprog Gprog f_number_add_inner number_add_inner_spec.
Proof.
  start_function.
  forward. forward. unfold make_number. forward_call.
  forward. forward. deadvars!. normalize.
  remember
    (Z.max (Zlength (number_digits left))
           (Zlength (number_digits right)))
  as max_length.
  forward_for_simple_bound max_length
  (EX j: Z,
   PROP ()
   LOCAL (
     temp _i (Vlong (Int64.repr max_length));
     lvar _carry tulong v_carry;
     temp _left left_pointer;
     temp _right right_pointer;
     temp _target output_pointer)
   SEP (
     cnumber left left_pointer;
     cnumber right right_pointer;
     data_at Tsh tulong (Vlong (Int64.repr 0)) v_carry;
     pre_cnumber output
       (Zlength (add_digits (number_digits left) (number_digits right)))
       output_pointer))%assert. {
    unfold digit_bound in H, H2; rep_lia.
  } {
    unfold cnumber, make_number; entailer!.
  } {
    admit.
  } {
    admit.
  }
Admitted.
