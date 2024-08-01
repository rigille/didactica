Require Import Coq.Program.Basics.

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.

Require Import Didactica.arithmetic.
Require Import Didactica.number.

Lemma body_number_add_inner: semax_body Vprog Gprog f_number_add_inner number_add_inner_spec.
Proof.
  start_function.
  forward. unfold make_number. forward.
  remember 
    (add_digits
      (number_digits left)
      (number_digits right))
  as total.
  remember
    (Zlength total)
  as final_length.
  (* TODO: prove theorems so that unfolding here is not necessary *)
  unfold pre_digit_array.
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
     data_at
       (pre_number_share output)
       struct_number
       (Vptrofs (Ptrofs.repr final_length), pre_number_array output)
       output_pointer;
      data_at
        (pre_number_share output)
        (tarray tulong final_length)
        (app
          (map
            (Vptrofs oo Ptrofs.repr)
            (sublist 0 j total))
          (Zrepeat Vundef (final_length - j)))
        (pre_number_array output)
    ))%assert. {
       admit. (* TODO *)
  } {
    admit.
  } {
    admit.
  } {
    replace (final_length - final_length) with 0 by lia.
    unfold Zrepeat, Z.to_nat, repeat.
    replace
      (map (Vptrofs oo Ptrofs.repr) (sublist 0 final_length total) ++ [])
    with
      (map (Vptrofs oo Ptrofs.repr) total)
    by list_solve.
    unfold cnumber, make_number, fill_number, writable_pre_number,
    readable_number.
    entailer!. {
      admit. (* TODO prove that addition repects bounds *)
    } 
  }
Admitted.
