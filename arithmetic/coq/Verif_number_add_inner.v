Require Import Coq.Program.Basics.

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.

Require Import Didactica.arithmetic.
Require Import Didactica.number.

Lemma body_number_add_inner: semax_body Vprog Gprog f_number_add_inner number_add_inner_full_spec.
Proof.
  start_function.
  forward. deadvars!. forward. unfold make_number.
  (*remember 
    (add_digits
      carry
      (number_digits left)
      (number_digits right))
  as total.
  remember
    (Zlength total)
  as final_length.
  unfold pre_digit_array, make_number. *)
  (* TODO: prove theorems so that unfolding here is not necessary *)
  remember (pre_number_length output) as limit.
  remember
    (add_digits
      carry
      (number_digits left)
      (number_digits right))
  as total.
  remember
    (Zlength total)
  as total_length.
  forward_for_simple_bound
  limit
  (EX j : Z, EX carry_out : bool,
   PROP (
     let trail_left :=
       (sublist j total_length (number_digits left)) in
     let trail_right :=
       (sublist j total_length (number_digits right)) in
     (eq
       (add_digits
         carry_out
         trail_left
         trail_right)
       (sublist
         j
         total_length
         total)))
   LOCAL (
     temp _limit (Vptrofs (Ptrofs.repr limit));
     temp _carry (Vlong (Int64.repr (Z.b2z carry))); 
     temp _left left_pointer; temp _right right_pointer;
     temp _target output_pointer)
   SEP (
     (cnumber left left_pointer);
     (cnumber right right_pointer);
     data_at
       (pre_number_share output)
       struct_number
       (Vptrofs (Ptrofs.repr limit), pre_number_array output)
       output_pointer;
     data_at
        (pre_number_share output)
        (tarray tulong (pre_number_length output))
        (app
          (map
            (Vptrofs oo Ptrofs.repr)
            (sublist 0 j total))
          (Zrepeat Vundef (total_length - j)))
        (pre_number_array output)))%assert. {
       unfold digit_bound in H; rep_lia.
  } {
    replace 
      (map (Vptrofs oo Ptrofs.repr) (sublist 0 0 total))
    with (@nil val) by list_solve.
    rewrite app_nil_l.
    entailer!.  entailer!.
  } {
    rewrite <- seq_assoc.
    forward_call. forward. deadvars!.
    rewrite <- seq_assoc.
    forward_call. forward. deadvars!.
    (* left_digit : Z, right_digit : Z,
       carry_in : bool, carry_out : val *)
    forward. (* forward_call (
      (Znth i (number_digits left)),
      (Znth i (number_digits right)),
      false,
      v_carry
    ). *) admit.
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
