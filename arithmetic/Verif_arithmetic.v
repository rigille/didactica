Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Didactica.Main.
Require Import Didactica.arithmetic.
Require Import VST.veric.version.
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
  !!(0 <= Zlength digit_list <= Int64.max_unsigned /\ Forall (fun d : Z => -1 < d < Int64.max_unsigned) digit_list) &&
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
  WITH sh : share, digit_list : list Z, digits : val, n : val, i : Z
  PRE [ tptr struct_number, tulong ]
    PROP ()
    PARAMS (n; Vptrofs (Ptrofs.repr i))
    SEP (cnumber sh digit_list digits n)
  POST [ tulong ]
    PROP ()
    RETURN (Vlong (Int64.repr (Znth i digit_list)))
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

Lemma sublist_clamp_high: forall i u (d : list Z),
  Zlength d <= u ->
  sublist i u d = sublist i (Zlength d) d.
Proof.
  intros.
  unfold sublist.
  rewrite firstn_same.
  rewrite firstn_same.
  reflexivity.
  rewrite <- ZtoNat_Zlength. lia.
  rewrite <- ZtoNat_Zlength. lia.
Qed.

Lemma Znth_to_nth: forall i (d : list Z),
  0 <= i ->
  Znth i d = nth (Z.to_nat i) d 0.
Proof.
  intros. unfold Znth. destruct (Z_lt_dec i 0). lia.
  reflexivity.
Qed.

Lemma Znth_over: forall i (d : list Z),
  (Zlength d) <= i ->
  Znth i d = 0.
Proof.
  intros. unfold Znth. destruct (Z_lt_dec i 0).
  remember (Zlength_nonneg d) as H1.
  lia. apply nth_overflow.
  rewrite <- ZtoNat_Zlength.
  lia.
Qed.

Lemma number_zeroes: forall b n,
  number b (repeat 0 n) = 0.
Proof.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Lemma number_app_zeroes: forall b l n,
  number b l = number b (app l (repeat 0 n)).
Proof.
  intros. unfold number.
  rewrite fold_right_app.
  replace (fold_right (fun h t : Z => t * b + h) 0 (repeat 0 n))
  with (number b (repeat 0 n)) by reflexivity.
  rewrite (number_zeroes b n). reflexivity.
Qed.

Lemma compare_repeat_zero_left: forall base n l0 l1,
  (1 < base) ->
  (Forall (fun d => -1 < d < base) l0) ->
  (Forall (fun d => -1 < d < base) l1) ->
  compare l0 l1 = compare (app l0 (repeat 0 n)) l1.
Proof.
  intros. rewrite (compare_correct base (app l0 (repeat 0 n)));
  try assumption. rewrite <- number_app_zeroes.
  rewrite <- compare_correct; try assumption. reflexivity.
  apply Forall_app. split. apply H0. induction n. apply Forall_nil.
  simpl. apply Forall_cons. lia. apply IHn.
Qed.

Lemma Znth_repeat_zero: forall i (l : list Z) n,
  Znth i l = Znth i (app l (repeat 0 n)).
Proof.
  intros. destruct (Z_lt_dec i (Zlength l)).
  - rewrite Znth_app1. reflexivity. apply l0.
  - rewrite Znth_app2. replace (Znth i l) with 0.
    assert (0 = default) by reflexivity. rewrite H.
    rewrite (Znth_repeat n (i - Zlength l)). reflexivity.
    rewrite Znth_overflow. reflexivity. lia. lia.
Qed.

Theorem compare_backwards_equal_length: forall i d0 d1,
  Zlength d0 = Zlength d1 ->
  let u := Zlength d0 in
  0 < i <= Zlength d0 ->
  let n0 := (Znth (i - 1) d0) in
  let n1 := (Znth (i - 1) d1) in
  (eq
    (compare (n0 :: (sublist i u d0)) (n1 :: (sublist i u d1)))
    (compare (sublist (i - 1) u d0) (sublist (i - 1) u d1))).
Proof.
  intros. rewrite (sublist_split (i - 1) i u).
  rewrite (sublist_split (i - 1) i u).
  remember (i - 1) as k. replace i with (k + 1) by lia.
  rewrite (sublist_len_1 k).
  rewrite (sublist_len_1 k). subst k. subst n0 n1.
  reflexivity.
  lia. lia. lia. lia. lia. lia.
Qed.

Lemma product_compare_eq : forall c,
  product_compare c Eq = c.
Proof.
  destruct c; reflexivity.
Qed.

Theorem compare_l_nil : forall base l,
  (Forall (fun d => -1 < d < base) l) ->
  compare l [] = Eq \/
  compare l [] = Gt.
Proof.
  intros. inversion H. left. reflexivity. subst. 
  simpl. destruct (match x with | 0 => true | _ => false end && forallb (fun n : Z => match n with | 0 => true | _ => false end) l0)%bool.
  - left. reflexivity.
  - right. reflexivity.
Qed.

Theorem compare_app_suffix : forall p0 s0 p1 s1,
  let c := compare s0 s1 in
  (eq (length p1) (length p0)) ->
  (c = Lt \/ c = Gt) ->
  (eq (compare (app p0 s0) (app p1 s1))  c).
Proof.
  induction p0 as [ | hp0 tp0]; intros.
  - destruct p1. reflexivity. discriminate H.
  - destruct p1 as [ | hp1 tp1]. discriminate H. 
    simpl. rewrite IHtp0.
    subst c; destruct H0; rewrite H0; reflexivity.
    simpl in H; inversion H; reflexivity.
    assumption.
Qed.

Theorem compare_empty_app_suffix : forall p s,
  let c := compare [] s in
  (c = Lt \/ c = Gt) ->
  (eq (compare [] (app p s)) c).
Proof.
  intros. subst c.
  assert (forallb (fun n : Z => (0 =? n)%Z) s = false).
  - destruct H; unfold compare in H; destruct (forallb (fun n => (0 =? n)%Z) s) eqn: Hs;
    try discriminate H; reflexivity.
  - assert (forall p', forallb (fun n : Z => (0 =? n)%Z) (app p' s) = false).
    + induction p'. assumption.
      remember (fun n : Z => (0 =? n)%Z) as is_zero. simpl. rewrite IHp'.
      apply andb_false_r.
    + induction p. reflexivity.
      unfold compare. remember (fun n : Z => (0 =? n)%Z)
      as is_zero. simpl.
      rewrite H0. rewrite H1.
      rewrite andb_false_r.
      reflexivity.
Qed.

Theorem compare_suffix_aux : forall i n0 n1,
  let l0 := Zlength n0 in
  let l1 := Zlength n1 in
  let c := compare (sublist i l0 n0) (sublist i l1 n1) in
  0 <= i <= l1 ->
  Zlength n0 <= Zlength n1 ->
  (c = Lt \/ c = Gt) -> (compare n0 n1 = c).
Proof.
  (* I quite like this proof, albeit it's long it's faily readable *)
  intros.
  destruct (Z_le_dec i (Zlength n0)) as [i_bound | i_bound].
  - rewrite <- sublist_same
    with (lo := 0) (hi := l0) (al := n0); try lia.
    rewrite <- sublist_same
    with (lo := 0) (hi := l1) (al := n1); try lia.
    rewrite (sublist_split 0 i _ n0); try lia.
    rewrite (sublist_split 0 i _ n1); try lia.
    intros.
    rewrite compare_app_suffix with
    (p0 := (sublist 0 i n0))
    (s0 := sublist i l0 n0) (p1 := (sublist 0 i n1))
    (s1 := sublist i l1 n1). reflexivity.
    rewrite <- ZtoNat_Zlength.
    rewrite <- ZtoNat_Zlength.
    rewrite Zlength_sublist; try lia.
    rewrite Zlength_sublist; try lia.
    subst c; assumption.
  - rewrite <- sublist_same
    with (lo := 0) (hi := l0) (al := n0); try lia.
    rewrite <- sublist_same
    with (lo := 0) (hi := l1) (al := n1); try lia.
    subst c.
    rewrite sublist_over with
      (i := i) (j := l0) (l := n0) in *; try lia.
    rewrite <- compare_empty_app_suffix with
      (p := sublist l0 i n1) (s := sublist i l1 n1) in *; try assumption.
    assert (0 <= l0) by list_solve.
    assert (0 <= l1) by list_solve.
    subst l0 l1.
    rewrite <- sublist_split in *; try lia.
    remember (Zlength n0) as l0.
    remember (Zlength n1) as l1.
    rewrite <- compare_app_suffix with
      (p0 := sublist 0 l0 n0) (s0 := [])
      (p1 := sublist 0 l0 n1) (s1 := (sublist l0 l1 n1));
    try assumption.
    rewrite <- sublist_split; try lia.
    rewrite app_nil_r. reflexivity.
    rewrite <- ZtoNat_Zlength.
    rewrite <- ZtoNat_Zlength.
    rewrite Zlength_sublist; try lia.
    rewrite Zlength_sublist; try lia.
Qed.

Theorem compare_suffix : forall i n0 n1,
  let u := Z.max (Zlength n0) (Zlength n1) in
  let c := compare (sublist i u n0) (sublist i u n1) in
  0 <= i <= u ->
  (c = Lt \/ c = Gt) ->
  (compare n0 n1 = c).
Proof.
  intros i n0 n1 u. rewrite sublist_clamp_high with (d := n0); try lia.
  rewrite sublist_clamp_high with (d := n1); try lia.
  destruct (Z_le_dec (Zlength n0) (Zlength n1)).
  - intros. subst c; rewrite compare_suffix_aux with
      (i := i) (n0 := n0) (n1 := n1); try assumption; try lia.
    reflexivity.
  - rewrite compare_antisym. rewrite compare_antisym with
    (digits0 := n0) (digits1 := n1).
    intros.
    rewrite compare_suffix_aux with
      (i := i) (n0 := n1) (n1 := n0); try assumption; try lia.
    reflexivity.
    destruct H0.
    + right. subst c.
      rewrite CompOpp_iff in H0.
      apply H0.
    + left. subst c.
      rewrite CompOpp_iff in H0.
      apply H0.
Qed.

Theorem compare_backwards: forall base i d0 d1,
  (1 < base) ->
  (Forall (fun d => -1 < d < base) d0) ->
  (Forall (fun d => -1 < d < base) d1) ->
  let u := Z.max (Zlength d0) (Zlength d1) in
  0 < i <= u ->
  let n0 := (Znth (i - 1) d0) in
  let n1 := (Znth (i - 1) d1) in
  (eq
    (compare (n0 :: (sublist i u d0)) (n1 :: (sublist i u d1)))
    (compare (sublist (i - 1) u d0) (sublist (i - 1) u d1))).
Proof.
  intros. simpl.
  destruct (Z_lt_dec (i - 1) (Zlength d0)).
  - rewrite (sublist_clamp_high i u d0); try lia.
    rewrite (sublist_clamp_high (i - 1) u d0); try lia.
    rewrite (sublist_split (i - 1) i (Zlength d0)); try lia.
    replace i with ((i - 1) + 1) at 4 by lia.
    rewrite (sublist_one (i - 1) _ d0); try lia.
    destruct (Z_lt_dec (i - 1) (Zlength d1)).
    + rewrite (sublist_clamp_high i u d1); try lia.
      rewrite (sublist_clamp_high (i - 1) u d1); try lia.
      rewrite (sublist_split (i - 1) i (Zlength d1)); try lia.
      replace i with ((i - 1) + 1) at 6 by lia.
      rewrite (sublist_one (i - 1) _ d1); try lia.
      reflexivity.
    + rewrite (sublist_over d1 (i - 1)); try lia.
      rewrite (sublist_over d1 i); try lia. subst n1.
      rewrite (Znth_over (i - 1) d1); try lia.
      subst n0.
      destruct (Z.compare (Znth (i - 1) d0) 0) eqn:H3.
      * apply Z.compare_eq in H3. rewrite -> H3.
        simpl. rewrite product_compare_eq.
        destruct (sublist i (Zlength d0) d0); reflexivity.
      * assert (-1 < Znth (i - 1) d0 < base).
        apply sublist.Forall_Znth. lia. assumption.
        destruct (Znth (i - 1) d0); try discriminate; try lia.
      * simpl. destruct (Znth (i - 1) d0); try discriminate.
        simpl. destruct (compare_l_nil base (sublist i (Zlength d0) d0)).
        apply Forall_sublist. apply H0.
        rewrite H4. reflexivity.
        rewrite H4. reflexivity.
  - subst n0. rewrite (sublist_over d0 (i - 1)); try lia.
    rewrite (sublist_over d0 i); try lia. rewrite Znth_over; try lia.
    destruct (Z_lt_dec (i - 1) (Zlength d1)).
    + rewrite (sublist_split (i - 1) i u); try lia.
      replace i with ((i - 1) + 1) at 3 by lia.
      rewrite (sublist_one (i - 1) _ d1); try lia. subst n1.
      destruct (Z.eq_decidable 0 (Znth (i - 1) d1)).
      rewrite <- H3. simpl.
      rewrite product_compare_eq. reflexivity.
      simpl. destruct (Znth (i - 1) d1) eqn:H4. lia.
      simpl. destruct (forallb (fun n0 : Z => match n0 with | 0 => true | _ => false end) (sublist i u d1)); reflexivity.
      exfalso. assert (-1 < Znth (i - 1) d1 < base).
      apply sublist.Forall_Znth. lia. assumption. lia.
    + lia.
Qed.

Lemma Znth_bounded : forall i base digits,
  1 < base ->
  0 <= i ->
  Forall (fun d : Z => -1 < d < base) digits ->
  -1 < Znth i digits < base.
Proof.
  intros. destruct (Z_lt_dec i (Zlength digits)).
  - apply sublist.Forall_Znth. lia. apply H1.
  - rewrite Znth_over. lia. lia.
Qed.


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
      0 <= i <= u;
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
      forward_call (sh0, d0, digits0, n0, (i - 1)).
      { unfold cnumber; entailer!. }
      { forward; deadvars!.
      rewrite <- seq_assoc.
      forward_call (sh1, d1, digits1, n1, (i - 1)).
      { unfold cnumber. entailer!. } {
      apply repr64_neq_e in HRE.
      normalize in HRE.
      unfold cnumber. Intros.
      forward; deadvars!.
      assert (eq (compare ((Znth (i - 1) d0) :: (sublist i u d0)) ((Znth (i - 1) d1) :: (sublist i u d1))) (compare (sublist (i - 1) u d0) (sublist (i - 1) u d1))).
      subst u.
      rewrite (compare_backwards Int64.max_unsigned i d0 d1).
      reflexivity. rep_lia.
      assumption.
      assumption.
      lia. simpl in H5.
      rewrite H4 in H5; simpl in H5.
      assert (-1 < Znth (i - 1) d1 < Int64.max_unsigned).
      apply Znth_bounded with
        (i := i - 1) (base := Int64.max_unsigned)
        (digits := d1); try rep_lia; assumption.
      assert (-1 < Znth (i - 1) d0 < Int64.max_unsigned).
      apply Znth_bounded with
        (i := i - 1) (base := Int64.max_unsigned)
        (digits := d0); try rep_lia; assumption.
      forward_if. replace ((Znth (i - 1) d0 ?= Znth (i - 1) d1)%Z) with
        Lt in *.
      forward. unfold cnumber; entailer!.
      rewrite compare_suffix with
        (i := i - 1); try lia.
      rewrite <- H5.
      reflexivity.
      left. symmetry. apply H5.
      forward_if. replace ((Znth (i - 1) d0 ?= @Znth Z 0 (i - 1) d1)%Z)
      with Gt in *. 
      forward.
      unfold cnumber; entailer!.
      rewrite compare_suffix with (i := i - 1); try lia.
      rewrite <- H5. reflexivity.
      right. symmetry.
      assumption. rewrite Z.compare_antisym.
      symmetry.
      rewrite CompOpp_iff.
      apply Zaux.Zcompare_Lt.
      assumption.
      forward. Exists (i - 1).
      entailer!.
      rewrite <- H5.
      apply Zaux.Zcompare_Eq.
      lia.
      } }
    } {
      apply repr_inj_unsigned64 in HRE; try lia.
      subst i. assert (compare d0 d1 = Eq).
      - rewrite (sublist_same_gen 0 u d1) in H4; try lia.
        rewrite (sublist_same_gen 0 u d0) in H4; try lia.
        apply H4.
      - forward. rewrite H5.
        unfold cnumber.
        entailer!.
    }
Qed.
