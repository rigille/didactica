Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Didactica.arithmetic.
Require Import Didactica.Main.
Require Import Didactica.Add.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Definition struct_number :=
  Tstruct _number noattr.

(* For some reason coq has trouble typechecking this if it's inlined *)
Definition make_number (l : Z) (v : val) : reptype struct_number :=
  ((Vptrofs (Ptrofs.repr l)), v).

Record number_data := build_number_data {
  sh : share;
  pointer : val;
  digits : list Z;
}.

(*
Definition number_data_example :=
  build_number_data Tsh (Vint (Int.repr 0)) [].

Compute (digits number_data_example).
*)

Definition digit_array
  {CS : compspecs} (sh : Share.t)
  (digit_list : list Z) (digits : val) := 
  (data_at
    sh
    (tarray tulong (Zlength digit_list))
    (map Vptrofs (map Ptrofs.repr digit_list))
    digits).

Definition uninitialized_digit_array
  {CS : compspecs} (sh : Share.t)
  (length : Z) (digits : val) :=
  (data_at_
    sh
    (tarray tulong length)
    digits).

Definition cnumber {CS : compspecs} (sh : Share.t)
  (digit_list : list Z) (digits : val) (p : val) :=
  (andp
    (prop 
      (and
        (0 <= Zlength digit_list <= Int64.max_unsigned)
      (and
        (Forall
          (fun d : Z => -1 < d < Int64.max_unsigned)
          digit_list)
        (nonempty_share sh))))
    (sepcon
      (data_at
        sh
        struct_number
        (make_number (Zlength digit_list) digits)
        p)
      (digit_array sh digit_list digits))).

Definition uninitialized_cnumber {CS : compspecs}
  (sh : Share.t) (size : Z) (digits : val)
  (p : val) :=
  (andp
    (prop (and
      (0 <= size <= Int64.max_unsigned)
      (nonempty_share sh)))
    (sepcon
      (data_at
        sh
        struct_number
        (make_number size digits)
        p)
      (uninitialized_digit_array
        sh size digits))).

Arguments digit_array CS sh digit_list digits : simpl never.
Arguments uninitialized_digit_array
            CS sh length digits : simpl never.

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

Definition number_add_inner_spec : ident * funspec :=
  DECLARE _number_add_inner
  WITH
    left : number_data, left_pointer : val,
    right : number_data, right_pointer : val,
    output_share : share, output_digits_pointer : val,
    output_pointer : val
  PRE [ tptr struct_number, tptr struct_number ]
    PROP (
      readable_share (sh left);
      readable_share (sh right);
      writable_share output_share)
    PARAMS (left_pointer; (pointer right); output_pointer)
    SEP (
      (cnumber
        (sh left) (digits left) (pointer left) left_pointer);
      (cnumber
        (sh right) (digits right) (pointer right) right_pointer);
      (uninitialized_cnumber
        output_share
        (Zlength
          (number_add Int64.max_unsigned (digits left) (digits right)))
        output_digits_pointer
        output_pointer))
  POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP (
      (cnumber
          (sh left) (digits left) (pointer left) left_pointer);
      (cnumber
        (sh right) (digits right) (pointer right) right_pointer);
      (cnumber
        output_share
        (number_add
          Int64.max_unsigned (digits left) (digits right))
        output_digits_pointer
        output_pointer)).

Definition Gprog : funspecs := [
  number_get_spec;
  max_size_t_spec;
  number_compare_spec;
  number_add_inner_spec
].
