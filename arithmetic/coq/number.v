Require Import Coq.Program.Basics.
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
  number_share : share;
  number_array : val;
  number_digits : list Z;
}.

Record pre_number_data := build_pre_number_data {
  pre_number_share : share;
  pre_number_array : val;
  pre_number_length : Z;
}.

Definition fill_number
  (data : pre_number_data) (digits : list Z) := 
  (build_number_data
    (pre_number_share data)
    (pre_number_array data)
    (sublist 0 (pre_number_length data) digits)).

(*
Definition number_data_example :=
  build_number_data Tsh (Vint (Int.repr 0)) [].

Compute (number_digits number_data_example).
*)

Definition digit_array
  {CS : compspecs} (data : number_data) := 
  (data_at
    (number_share data)
    (tarray tulong (Zlength (number_digits data)))
    (map (compose Vptrofs Ptrofs.repr) (number_digits data))
    (number_array data)).

Definition pre_digit_array
  {CS : compspecs} (data : pre_number_data) :=
  (data_at_
    (pre_number_share data)
    (tarray tulong (pre_number_length data))
    (pre_number_array data)).

Definition digit_bound (digit : Z) :=
  -1 < digit < Int64.modulus.

Definition readable_number (data : number_data) :=
  readable_share (number_share data).

Definition writable_number (data : number_data) :=
  writable_share (number_share data).

Definition writable_pre_number (data : pre_number_data) :=
  writable_share (pre_number_share data).

Definition cnumber {CS : compspecs}
  (data : number_data) (pointer : val) :=
  let digit_list := (number_digits data) in
  let length := (Zlength digit_list) in
  (andp
    (prop 
      (and
        (digit_bound length)
      (and
        (Forall digit_bound digit_list)
        (readable_number data))))
    (sepcon
      (data_at
        (number_share data)
        struct_number
        (make_number length (number_array data))
        pointer)
      (digit_array data))).

Definition pre_cnumber {CS : compspecs}
  (data : pre_number_data) (pointer : val) :=
  (andp
    (prop (and
      (digit_bound (pre_number_length data))
      (writable_pre_number data)))
    (sepcon
      (data_at
        (pre_number_share data)
        struct_number
        (make_number (pre_number_length data) (pre_number_array data))
        pointer)
      (pre_digit_array data))).

Arguments digit_array CS data : simpl never.
Arguments pre_digit_array
            CS data : simpl never.

Arguments cnumber CS data pointer : simpl never.

Lemma cnumber_local_facts:
  forall data pointer,
   cnumber data pointer |--
       !! (isptr pointer /\ digit_bound (Zlength (number_digits data))).
Proof.
  intros. unfold cnumber. entailer!.
Qed.

Lemma cnumber_valid_pointer:
  forall data pointer,
   cnumber data pointer |-- valid_pointer pointer.
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

Definition add_digits : bool -> list Z -> list Z -> list Z :=
  number_add Int64.modulus.

Definition digits_full_adder : bool -> Z -> Z -> (bool * Z) :=
  full_adder Int64.modulus.

Definition number_get_spec : ident * funspec :=
  DECLARE _number_get
  WITH data : number_data, n : val, i : Z
  PRE [ tptr struct_number, tulong ]
    PROP ()
    PARAMS (n; Vptrofs (Ptrofs.repr i))
    SEP (cnumber data n)
  POST [ tulong ]
    PROP ()
    RETURN (Vlong (Int64.repr (Znth i (number_digits data))))
    SEP (cnumber data n).

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
   data0 : number_data, data1 : number_data,
   n0 : val, n1 : val
 PRE [ tptr struct_number, tptr struct_number ]
   PROP ()
   PARAMS (n0; n1)
   SEP (cnumber data0 n0; cnumber data1 n1)
 POST [ tint ]
   PROP ()
   RETURN (
     comparison_int (compare
       (number_digits data0)
       (number_digits data1)))
   SEP (cnumber data0 n0; cnumber data1 n1).

Definition add_with_carry_spec : ident * funspec :=
  DECLARE _add_with_carry
  WITH
    left_digit : Z, right_digit : Z, carry_in : bool,
    carry_out : val
  PRE [tulong, tulong, tulong, tptr tulong]
    PROP (
      digit_bound left_digit;
      digit_bound right_digit)
    PARAMS (
      Vlong (Int64.repr left_digit);
      Vlong (Int64.repr right_digit);
      Vlong (Int64.repr (Z.b2z carry_in));
      carry_out)
    SEP (data_at_ Tsh tulong carry_out)
  POST [ tulong ]
    PROP ()
    RETURN (
      Vlong (Int64.repr
        (snd (digits_full_adder
          carry_in left_digit right_digit))))
    SEP(
      (data_at
        Tsh
        tulong
        (Vlong (Int64.repr
          (Z.b2z (fst (digits_full_adder
            carry_in
            left_digit
            right_digit)))))
        carry_out)
    ).

Definition number_add_inner_spec : ident * funspec :=
  DECLARE _number_add_inner
  WITH
    carry : bool, left : number_data, left_pointer : val,
    right : number_data, right_pointer : val,
    output : pre_number_data, output_pointer : val
  PRE [ tulong, tptr struct_number, tptr struct_number, tptr struct_number ]
    PROP ()
    PARAMS (
      Vlong (Int64.repr (Z.b2z carry));
      left_pointer; right_pointer; output_pointer)
    SEP (
      (cnumber left left_pointer);
      (cnumber right right_pointer);
      (pre_cnumber output output_pointer))
  POST [ tvoid ]
    EX carry_out : bool,
    PROP (
      let output_length := pre_number_length output in
      let total :=
        (add_digits
          carry
          (number_digits left)
          (number_digits right)) in
      let total_length := Zlength total in
      let trail_left :=
        (sublist output_length total_length (number_digits left)) in
      let trail_right :=
        (sublist output_length total_length (number_digits right)) in
      (eq
        (add_digits
          carry_out
          trail_left
          trail_right)
        (sublist
          output_length
          total_length
          total)))
    RETURN (Vlong (Int64.repr (Z.b2z carry_out)))
    SEP (
      (cnumber left left_pointer);
      (cnumber right right_pointer);
      (cnumber
        (fill_number
          output
          (add_digits carry (number_digits left) (number_digits right)))
        output_pointer)).

Definition Gprog : funspecs := [
  number_get_spec;
  max_size_t_spec;
  number_compare_spec;
  number_add_inner_spec;
  add_with_carry_spec
].
