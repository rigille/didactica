Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Didactica.Main.
Require Import Didactica.arithmetic.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Definition struct_number := Tstruct _number noattr.

(* For some reason coq has trouble typechecking this if it's inlined *)
Definition make_number (l : list Z) (v : val) : reptype struct_number :=
  ((Vint (Int.repr (Zlength l))), v).

Definition cnumber {CS : compspecs} (sh : Share.t) (digit_list : list Z) (p : val) :=
  EX digits : val,
  data_at Ews struct_number (make_number digit_list digits) p *
  data_at sh (tarray tulong (Zlength digit_list)) (map Vint (map Int.repr digit_list)) digits.

Lemma cnumber_local_facts:
  forall sh digit_list p,
   cnumber sh digit_list p |--
   !! (isptr p).
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
    SEP (cnumber sh0 d0 n0 * cnumber sh1 d1 n1)
  POST [ tint ]
    PROP ()
    RETURN (comparison_int (compare d0 d1))
    SEP (cnumber sh0 d0 n0 * cnumber sh1 d1 n1).

Definition Gprog : funspecs := [ number_compare_spec ].

Lemma body_number_compare: semax_body Vprog Gprog f_number_compare number_compare_spec.
Proof.
  start_function.
Admitted.
