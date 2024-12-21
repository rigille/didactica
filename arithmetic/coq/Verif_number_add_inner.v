Require Import Coq.Program.Basics.

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.

Require Import Didactica.arithmetic.
Require Import Didactica.number.
Require Import Didactica.sublist.
Require Import Didactica.Add.

Lemma body_number_add_inner: semax_body Vprog Gprog f_number_add_inner number_add_inner_full_spec.
Proof.
  start_function.
  forward. unfold make_number.
  remember (pre_number_length output) as limit.
  remember
    (add_digits
      carry
      (number_digits left)
      (number_digits right)
      (Z.to_nat limit))
  as final_results.
  remember (fst final_results) as total.
  forward_for_simple_bound
  limit
  (EX j : Z, EX carry_out : bool,
   EX results : list Z * bool,
   PROP (
     results =
       (add_digits
         carry
         (number_digits left)
         (number_digits right)
         (Z.to_nat j));
     carry_out = (snd results)
   )
   LOCAL (
     temp _limit (Vptrofs (Ptrofs.repr limit));
     temp _carry carry_pointer;
     temp _left left_pointer;
     temp _right right_pointer;
     temp _target output_pointer)
   SEP (
     bool_at carry_out carry_pointer;
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
            (fst results))
          (Zrepeat Vundef (limit - j)))
        (pre_number_array output)))%assert. {
       unfold digit_bound, base_bound in H; rep_lia.
  } {
       unfold digit_bound, base_bound in H; rep_lia.
  } {
    Exists carry.
    Exists (@nil Z, carry).
    entailer!. rewrite app_nil_l.
    unfold pre_digit_array.
    entailer!.
  } {
    (* prove loop invariant is preserved by loop body *)
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
    (*replace
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
     entailer!. *)
    admit.
  } {
    (* proof that loop invariant implies spec *)
    Intros carry_out.
    Intros results.
    Exists limit.
    Exists results.
    replace
      (limit - limit)
    with 0 by lia.
    (* unfold Zrepeat, Z.to_nat, repeat. *)
    rewrite app_nil_r.
    entailer!.
    remember
      (fst
        (add_digits carry (number_digits left)
           (number_digits right) (Z.to_nat (pre_number_length output))))
    as result.
    unfold fill_number, cnumber, digit_array, number_digits,
    number_array, readable_number, number_share, make_number.
    replace (Zlength result) with (pre_number_length output).
    entailer!. {
      (* proof that addition repects bounds *)
      apply number_add_bound. rep_lia.
      apply H4. apply H6.
    } {
      rewrite Zlength_correct.
      subst result.
      unfold add_digits.
      rewrite number_add_length.
      rewrite Z2Nat.id.
      reflexivity.
      unfold digit_bound, base_bound in H.
      lia.
    }
Admitted.
