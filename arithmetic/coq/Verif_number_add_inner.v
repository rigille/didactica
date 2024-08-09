Require Import Coq.Program.Basics.

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.

Require Import Didactica.arithmetic.
Require Import Didactica.number.
Require Import Didactica.sublist.

Lemma body_number_add_inner: semax_body Vprog Gprog f_number_add_inner number_add_inner_full_spec.
Proof.
  start_function.
  forward. unfold make_number.
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
    remember
      (add_digits
        carry
        (number_digits left)
        (number_digits right))
    as total.
    remember
      (Zlength total)
    as total_length.
    assert
      ((Zlength (number_digits left)) <= total_length) by admit.
    rewrite sublist_clamp_high; try assumption.
    assert
      ((Zlength (number_digits right)) <= total_length) by admit.
    rewrite (sublist_clamp_high 0 total_length); try assumption.
    replace
      (sublist 0 (Zlength (number_digits left)) (number_digits left))
    with
      (number_digits left)
    by list_solve.
    replace
      (sublist
        0 (Zlength (number_digits right)) (number_digits right))
    with
      (number_digits right)
    by list_solve.
    replace (sublist 0 total_length total) with total by list_solve.
    symmetry. apply Heqtotal.
    simpl. unfold pre_digit_array.
    entailer!.
  } {
    rewrite <- seq_assoc.
    forward_call. Intros vret; subst vret.
    forward. deadvars!. 
    rewrite <- seq_assoc.
    forward_call. forward. deadvars!.
    forward. rewrite <- seq_assoc.
    unfold cnumber. Intros.
    forward_call.
    split;
    apply Znth_bounded;
    unfold digit_bound; try assumption; try rep_lia.
    forward. deadvars!.
    remember
      (digits_full_adder carry_out
        (Znth i (number_digits left))
        (Znth i (number_digits right)))
    as full_adder_result.
    remember (snd full_adder_result) as new_digit.
    remember (fst full_adder_result) as new_carry.
    forward. forward.
    Exists new_carry.
    replace 
      (upd_Znth i
        (app
          (map
            (Vptrofs oo Ptrofs.repr)
            (sublist 0 i total))
          (Zrepeat Vundef (limit - i)))
        (Vlong (Int64.repr new_digit)))
    with
      (app
        (map (Vptrofs oo Ptrofs.repr) (sublist 0 (i + 1) total))
        (Zrepeat Vundef (limit - (i + 1)))).
    replace
      (add_digits new_carry
            (sublist (i + 1) total_length (number_digits left))
            (sublist (i + 1) total_length (number_digits right)))
    with
      (sublist (i + 1) total_length total).
    unfold cnumber.
    entailer!. {
      (* proof carry is correct *)
      admit.
    } {
      (* proof that written digit is correct *)
      Check Zrepeat_app.   (* Hint: this lemma will be useful. *)
      Check upd_Znth_app1. (* Hint: this lemma will be useful. *)
      Check app_Znth2.     (* Hint: this lemma will be useful. *)
      Check Znth_0_cons.   (* Hint: this lemma will be useful. *)
      admit.
    }
  } {
    Intros carry_out.
    Exists carry_out.
    entailer!.
    replace
      (pre_number_length output - pre_number_length output)
    with 0 by lia.
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
    admit. (*
    replace
      (Zlength
        (sublist 0 (pre_number_length output)
           (add_digits
             carry
             (number_digits left)
             (number_digits right)) ++
         Zrepeat 0
           (pre_number_length output
              - Zlength
                  (add_digits carry (number_digits left)
                     (number_digits right)))))
    with
      (pre_number_length output)
    by admit.
    entailer!. {
      admit. (* TODO prove that addition repects bounds *)
    } *)
  }
Admitted.
