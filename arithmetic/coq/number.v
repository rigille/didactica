Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Didactica.arithmetic.
Require Import Didactica.Main.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Definition struct_number := Tstruct _number noattr.

(* For some reason coq has trouble typechecking this if it's inlined *)
Definition make_number (l : list Z) (v : val) : reptype struct_number :=
  ((Vptrofs (Ptrofs.repr (Zlength l))), v).

Definition digit_array
  {CS : compspecs} (sh : Share.t)
  (digit_list : list Z) (digits : val) := 
  data_at
    sh
    (tarray tulong (Zlength digit_list))
    (map Vptrofs (map Ptrofs.repr digit_list))
    digits.

Arguments digit_array CS sh digit_list digits : simpl never.

Definition cnumber {CS : compspecs} (sh : Share.t)
  (digit_list : list Z) (digits : val) (p : val) :=
  !!(0 <= Zlength digit_list <= Int64.max_unsigned
     /\ Forall (fun d : Z => -1 < d < Int64.max_unsigned) digit_list) &&
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
 WITH
   sh0 : share, sh1: share, n0 : val, n1 : val,
   digits0 : val, digits1 : val, d0 : list Z, d1 : list Z
 PRE [ tptr struct_number, tptr struct_number ]
   PROP (readable_share sh0; readable_share sh1)
   PARAMS (n0; n1)
   SEP (cnumber sh0 d0 digits0 n0; cnumber sh1 d1 digits1 n1)
 POST [ tint ]
   PROP ()
   RETURN (comparison_int (compare d0 d1))
   SEP (cnumber sh0 d0 digits0 n0; cnumber sh1 d1 digits1 n1).

(*
Definition number_add_inner_spec : ident * funspec :=
  DECLARE _number_add_inner
  WITH
    sh0: share, sh1 : share, sh2 : share,
    n0 : val, n1 : val, r2 : val,
    digits0 : val, digits1 : val,
    d0 : list Z, d1 : list Z
  PRE [ tptr struct_number, tptr struct_number ]
    PROP (
      readable_share sh0;
      readable_share sh1;
      writable_share sh2)
    PARAMS (n0; n1; r2)
    SEP (
      cnumber sh0 d0 digits0 n0;
      cnumber sh1 d1 digits1 n1;
      )
*)


Definition Gprog : funspecs := [
  number_get_spec;
  max_size_t_spec;
  number_compare_spec
].
