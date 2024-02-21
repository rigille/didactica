Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Didactica.Main.
Require Import Didactica.arithmetic.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Definition struct_number := Tstruct _number noattr.

(* For some reason coq has trouble typechecking this if it's inlined *)
Definition make_number (l : list Z) (v : val) : reptype struct_number :=
  ((Vptrofs (Ptrofs.repr (Zlength l))), v).

Definition digit_array {CS : compspecs} (sh : Share.t) (digit_list : list Z) (digits : val) := 
  data_at sh (tarray tulong (Zlength digit_list)) (map Vptrofs (map Ptrofs.repr digit_list)) digits.

Definition cnumber {CS : compspecs} (sh : Share.t) (digit_list : list Z) (p : val) :=
  EX digits : val,
  !!(0 <= Zlength digit_list <= Int64.max_unsigned) &&
  data_at Ews struct_number (make_number digit_list digits) p *
  digit_array sh digit_list digits.

Lemma cnumber_local_facts:
  forall sh digit_list p,
   cnumber sh digit_list p |--
       !! (isptr p /\ 0 <= Zlength digit_list <= Int64.max_unsigned).
Proof.
  intros. unfold cnumber. Intros digits. entailer!.
Qed.

Lemma cnumber_valid_pointer:
  forall sh digit_list p,
   cnumber sh digit_list p |-- valid_pointer p.
Proof.
  intros. unfold cnumber. Intros digits. entailer!.
Qed.

#[export] Hint Resolve cnumber_local_facts : saturate_local.
#[export] Hint Resolve cnumber_valid_pointer : valid_pointer.

Definition comparison_int c : val :=
  match c with
  | Lt => Vint (Int.repr (-1))
  | Eq => Vint (Int.repr 0)
  | Gt => Vint (Int.repr 1)
  end.

Definition number_compare_spec : ident * funspec :=
 DECLARE _number_compare
  WITH sh0: share, sh1: share, n0 : val, n1 : val, d0 : list Z, d1 : list Z
  PRE [ tptr struct_number, tptr struct_number ]
    PROP (readable_share sh0; readable_share sh1)
    PARAMS (n0; n1)
    SEP (cnumber sh0 d0 n0; cnumber sh1 d1 n1)
  POST [ tint ]
    PROP ()
    RETURN (comparison_int (compare d0 d1))
    SEP (cnumber sh0 d0 n0; cnumber sh1 d1 n1).

Definition Gprog : funspecs := [ number_compare_spec ].

Lemma body_number_compare: semax_body Vprog Gprog f_number_compare number_compare_spec.
Proof.
  start_function.
  unfold cnumber. Intros digits0 digits1.
  forward.
  forward. simpl.
  forward_if (
    PROP ( )
    LOCAL (
      temp _t'1  (Vptrofs (Ptrofs.repr (Z.max (Zlength d1) (Zlength d0))));
      temp _t'11 (Vptrofs (Ptrofs.repr (Zlength d1)));
      temp _t'10 (Vptrofs (Ptrofs.repr (Zlength d0))); 
      temp _left n0; temp _right n1
    )
    SEP (
      data_at Ews struct_number (make_number d0 digits0) n0;
      digit_array sh0 d0 digits0;
      data_at Ews struct_number (make_number d1 digits1) n1;
      digit_array sh1 d1 digits1
    )
  ).
  - forward; forward. entailer!. rewrite Z.max_l.
    reflexivity. lia.
  - forward; forward. entailer!. rewrite Z.max_r.
    reflexivity. lia.
  - forward. Search skipn.
    Print sublist. Search sublist.
    remember (Z.max (Zlength d1) (Zlength d0)) as u.
    forward_while (
      EX i : Z,
      PROP (
        0 <= i <= Int64.max_unsigned;
        compare (sublist i u d0) (sublist i u d1) = Eq
      )
      LOCAL (
        temp _i (Vptrofs (Ptrofs.repr i));
        temp _t'1 (Vptrofs (Ptrofs.repr (Z.max (Zlength d1) (Zlength d0))));
        temp _t'11 (Vptrofs (Ptrofs.repr (Zlength d1)));
        temp _t'10 (Vptrofs (Ptrofs.repr (Zlength d0))); 
        temp _left n0; temp _right n1
      )
      SEP (
        data_at Ews struct_number (make_number d0 digits0) n0;
        digit_array sh0 d0 digits0;
        data_at Ews struct_number (make_number d1 digits1) n1;
        digit_array sh1 d1 digits1
      )
    ). Exists u. entailer!. {
      remember (Z.max (Zlength d1) (Zlength d0)) as u.
      Search sublist. rewrite (sublist_over d1 u u).
      rewrite (sublist_over d0 u u). reflexivity.
      lia. lia.
    } { entailer!. } {
      admit.
    } {
      Search (Int64.repr).
      apply (repr_inj_unsigned64 _ _ H1) in HRE.
      subst i. assert (compare d0 d1 = Eq).
      - Search (sublist _ _ ?a = ?a).
        rewrite (sublist_same_gen 0 u d1) in H2; try lia.
        rewrite (sublist_same_gen 0 u d0) in H2; try lia.
        apply H2.
      - forward. rewrite H3.
        unfold cnumber.
        Exists digits0 digits1. 
        entailer!.
      - lia.
    }
Admitted.
