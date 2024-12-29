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
   EX results : bool * list Z,
   PROP (
     results =
       (add_digits
         carry
         (number_digits left)
         (number_digits right)
         (Z.to_nat j));
     carry_out = (fst results)
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
            (snd results))
          (Zrepeat Vundef (limit - j)))
        (pre_number_array output)))%assert. {
       unfold digit_bound, base_bound in H; rep_lia.
  } {
       unfold digit_bound, base_bound in H; rep_lia.
  } {
    Exists carry.
    Exists (carry, @nil Z).
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
    remember
      (add_digits carry (number_digits left)
        (number_digits right) (Z.to_nat (i + 1)))
    as new_results.
    Exists new_results.
    replace
      (upd_Znth i
        (map (Vptrofs oo Ptrofs.repr) (snd results) ++
        Zrepeat Vundef (limit - i)) (Vlong (Int64.repr new_digit)))
    with
      (app
        (map (Vptrofs oo Ptrofs.repr) (snd new_results))
        (Zrepeat Vundef (limit - (i + 1)))) by admit.
    unfold cnumber.
    entailer!.
    Print Znth.
    (* I need to prove that we can compose invocations of
       number_add *)
    unfold add_digits, number_add, add_aux; fold add_aux.
    remember
      (combine_default 0 0 (Z.to_nat i) (number_digits left)
        (number_digits right))
    as l.
    Search Znth.
    rewrite Znth_to_nth; try lia.
    rewrite Znth_to_nth; try lia.
    rewrite Z2Nat.inj_add; try lia.
    replace
      (Nat.add (Z.to_nat i) (Z.to_nat 1))
    with
      (S (Z.to_nat i)) by lia.
    Check next_carry.
    unfold digits_full_adder.
    Check number_add.
    replace
      (fold_map (number_add_body Int64.modulus) carry l)
    with
      (number_add Int64.modulus carry (number_digits left) (number_digits right) (Z.to_nat i))
    .
    rewrite next_carry.
    reflexivity.
    subst l.
    reflexivity.
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
      (snd
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
