Require Import Coq.Program.Basics.

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.

Require Import Didactica.arithmetic.
Require Import Didactica.number.

Lemma body_number_add_inner: semax_body Vprog Gprog f_number_add_inner number_add_inner_full_spec.
Proof.
  start_function.
  forward. unfold make_number.
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
     temp _carry carry_pointer;
     temp _left left_pointer;
     temp _right right_pointer;
     temp _target output_pointer)
   SEP (
     data_at Tsh tulong (Vlong (Int64.repr (Z.b2z carry_out))) carry_pointer;
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
          (Zrepeat Vundef (limit - j)))
        (pre_number_array output)))%assert. {
       unfold digit_bound in H; rep_lia.
  } {
       unfold digit_bound in H; rep_lia.
  } {
    Exists carry. entailer!.
    admit. admit. (*
    replace 
      (map (Vptrofs oo Ptrofs.repr) (sublist 0 0 total))
    with (@nil val) by list_solve.
    rewrite app_nil_l.
    entailer!.  entailer!.
    *)
  } {
    admit. (*
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
    ). *) *)
  } {
    Intros carry_out.
    Exists carry_out.
    entailer!.
    replace (pre_number_length output - pre_number_length output) with 0 by lia.
    unfold Zrepeat, Z.to_nat, repeat.
    replace
      (map ((fun x : ptrofs => Vlong (Ptrofs.to_int64 x)) oo Ptrofs.repr)
         (sublist 0 (pre_number_length output)
            (add_digits carry (number_digits left) (number_digits right))) ++
       [])
    with
      (map (Vptrofs oo Ptrofs.repr) (sublist 0 (pre_number_length output)
            (add_digits carry (number_digits left) (number_digits right))))
    by list_solve.
    unfold fill_number.
    unfold cnumber, make_number, fill_number, writable_pre_number,
    readable_number, digit_array. simpl.
    replace
      (Zlength
        (sublist 0 (pre_number_length output)
           (add_digits carry (number_digits left)
              (number_digits right))))
    with
      (pre_number_length output)
    by admit.
    entailer!. {
      admit. (* TODO prove that addition repects bounds *)
    }
  }
Admitted.
