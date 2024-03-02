Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Didactica.Main.
Require Import Didactica.arithmetic.
Require Import VST.veric.version.
Print release.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Definition struct_number := Tstruct _number noattr.

(* For some reason coq has trouble typechecking this if it's inlined *)
Definition make_number (l : list Z) (v : val) : reptype struct_number :=
  ((Vptrofs (Ptrofs.repr (Zlength l))), v).

Definition digit_array {CS : compspecs} (sh : Share.t) (digit_list : list Z) (digits : val) := 
  data_at sh (tarray tulong (Zlength digit_list)) (map Vptrofs (map Ptrofs.repr digit_list)) digits.

Arguments digit_array CS sh digit_list digits : simpl never.

Definition cnumber {CS : compspecs} (sh : Share.t) (digit_list : list Z) (digits : val) (p : val) :=
  !!(0 <= Zlength digit_list <= Int64.max_unsigned) &&
  (sepcon (data_at Ews struct_number (make_number digit_list digits) p)
          (digit_array sh digit_list digits)).

Arguments cnumber CS sh digit_list digits p : simpl never.

Lemma cnumber_local_facts:
  forall sh digit_list digits p,
   cnumber sh digit_list digits p |--
       !! (isptr p /\ 0 <= Zlength digit_list <= Int64.max_unsigned).
Proof.
  intros. unfold cnumber. entailer!.
Qed.

Lemma cnumber_valid_pointer:
  forall sh digit_list digits p,
   cnumber sh digit_list digits p |-- valid_pointer p.
Proof.
  intros. unfold cnumber. entailer!.
Qed.

#[export] Hint Resolve cnumber_local_facts : saturate_local.
#[export] Hint Resolve cnumber_valid_pointer : valid_pointer.

Definition comparison_int c : val :=
  match c with
  | Lt => Vint (Int.repr (-1))
  | Eq => Vint (Int.repr 0)
  | Gt => Vint (Int.repr 1)
  end.

Definition number_get_spec : ident * funspec :=
  DECLARE _number_get
  WITH sh : share, digit_list : list Z, digits : val, n : val, i : Z, d : Z
  PRE [ tptr struct_number, tulong, tulong ]
    PROP ()
    PARAMS (n; Vptrofs (Ptrofs.repr i); (Vlong (Int64.repr d)))
    SEP (cnumber sh digit_list digits n)
  POST [ tulong ]
    PROP ()
    RETURN (Vlong (Int64.repr (nth (Z.to_nat i) digit_list d)))
    SEP (cnumber sh digit_list digits n).

Definition max_size_t_spec : ident * funspec :=
  DECLARE _max_size_t
  WITH a : Z, b : Z
  PRE [ tulong, tulong ]
    PROP ()
    PARAMS (Vptrofs (Ptrofs.repr a); Vptrofs (Ptrofs.repr b))
    SEP ()
  POST [ tulong ]
    PROP ()
    RETURN (Vptrofs (Ptrofs.repr (Z.max a b)))
    SEP ().

Definition number_compare_spec : ident * funspec :=
 DECLARE _number_compare
  WITH sh0 : share, sh1: share, n0 : val, n1 : val, digits0 : val, digits1 : val, d0 : list Z, d1 : list Z
  PRE [ tptr struct_number, tptr struct_number ]
    PROP (readable_share sh0; readable_share sh1)
    PARAMS (n0; n1)
    SEP (cnumber sh0 d0 digits0 n0; cnumber sh1 d1 digits1 n1)
  POST [ tint ]
    PROP ()
    RETURN (comparison_int (compare d0 d1))
    SEP (cnumber sh0 d0 digits0 n0; cnumber sh1 d1 digits1 n1).

Definition Gprog : funspecs := [
  number_get_spec;
  max_size_t_spec;
  number_compare_spec
].

Locate Znth.

Lemma body_number_compare: semax_body Vprog Gprog f_number_compare number_compare_spec.
Proof.
  start_function.
  unfold cnumber. Intros.
  forward.
  forward. simpl.
  forward_call. forward. deadvars!.
  remember (Z.max (Zlength d0) (Zlength d1)) as u.
  forward_while (
    EX i : Z,
    PROP (
      0 <= i <= Int64.max_unsigned;
      compare (sublist i u d0) (sublist i u d1) = Eq
    )
    LOCAL (
      temp _i (Vptrofs (Ptrofs.repr i));
      temp _left n0; temp _right n1
    )
    SEP (
      data_at Ews struct_number (make_number d0 digits0) n0;
      digit_array sh0 d0 digits0;
      data_at Ews struct_number (make_number d1 digits1) n1;
      digit_array sh1 d1 digits1
    )
  ). Exists u. entailer!. {
      remember (Z.max (Zlength d0) (Zlength d1)) as u.
      rewrite (sublist_over d1 u u). rewrite (sublist_over d0 u u).
      reflexivity. lia. lia.
    } { entailer!. } {
      forward.
      rewrite <- seq_assoc.
      replace
        (Vlong (Int64.sub
                 (Ptrofs.to_int64 (Ptrofs.repr i))
                 (Int64.repr (Int.signed (Int.repr 1)))))
      with
        (Vptrofs (Ptrofs.repr (i - 1)))
      by normalize.
      forward_call (sh0, d0, digits0, n0, (i - 1), 0).
      { unfold cnumber; entailer!. }
      { forward; deadvars!.
      rewrite <- seq_assoc.
      forward_call (sh1, d1, digits1, n1, (i - 1), 0).
      { unfold cnumber. entailer!. } {
       unfold cnumber. Intros.
      forward; deadvars!.
      forward_if. admit.
      forward_if. admit.
      forward. Exists (i - 1).
      entailer!. admit.
      } }
    } {
      apply (repr_inj_unsigned64 _ _ H1) in HRE.
      subst i. assert (compare d0 d1 = Eq).
      - rewrite (sublist_same_gen 0 u d1) in H2; try lia.
        rewrite (sublist_same_gen 0 u d0) in H2; try lia.
        apply H2.
      - forward. rewrite H3.
        unfold cnumber.
        entailer!.
      - lia.
    }
Admitted.

Lemma sublist_clamp_high: forall {X} i u (d : list X),
  Zlength d <= u ->
  sublist i u d = sublist i (Zlength d) d.
Proof.
Admitted.

Lemma Znth_to_nth: forall i (d : list Z),
  0 <= i ->
  Znth i d = nth (Z.to_nat i) d 0.
Proof.
  intros. unfold Znth. destruct (Z_lt_dec i 0). lia.
  reflexivity.
Qed.

Theorem compare_backwards: forall i d0 d1,
  let u := Z.max (Zlength d0) (Zlength d1) in
  0 < i <= u ->
  let n0 := (Znth (i - 1) d0) in
  let n1 := (Znth (i - 1) d1) in
  (eq
    (compare (n0 :: (sublist i u d0)) (n1 :: (sublist i u d1)))
    (compare (sublist (i - 1) u d0) (sublist (i - 1) u d1))).
Proof.
  intros.
  rewrite (sublist_clamp_high i u d0); try lia.
  rewrite (sublist_clamp_high (i - 1) u d0); try lia.
  rewrite (sublist_clamp_high i u d1); try lia.
  rewrite (sublist_clamp_high (i - 1) u d1); try lia.
  destruct (Z_le_gt_dec (Zlength d0) (i - 1)).
  - rewrite (sublist_over d0); try lia.
    rewrite (sublist_over d0); try assumption.
    destruct (Z_le_gt_dec (Zlength d1) (i - 1)).
    lia.
  Check sublist_split.
    rewrite (sublist_split (i - 1) i (Zlength d1)); try lia.
    rewrite sublist_one; try lia.

    rewrite <- (sublist_suffix 0
    Search sublist.
    destruct (Z_le_gt_dec (Zlength d1) i).
    + assert (i >= u) by lia.
      
