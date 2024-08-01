Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Didactica.arithmetic.
Require Import Didactica.number.

Lemma body_number_add_inner: semax_body Vprog Gprog f_number_add_inner number_add_inner_spec.
Proof.
  start_function.
  forward. unfold make_number. forward.
  remember
    (Zlength (add_digits
      (number_digits left)
      (number_digits right)))
  as final_length.
  forward_for_simple_bound
  final_length
  (EX j: Z,
   PROP ()
   LOCAL (
     temp _limit (Vlong (Int64.repr final_length));
     lvar _carry tulong v_carry;
     temp _left left_pointer;
     temp _right right_pointer;
     temp _target output_pointer)
   SEP (
     cnumber left left_pointer;
     cnumber right right_pointer;
     data_at Tsh tulong (Vlong (Int64.repr 0)) v_carry;
     pre_cnumber output final_length output_pointer))%assert. {
       admit. (* TODO *)
  } {
    unfold cnumber, pre_cnumber, make_number; entailer!.
  } {
    admit.
  } {
    admit.
  }
Admitted.
