Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Didactica.Main.
Require Import Didactica.arithmetic.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Definition t_number := Tstruct _number noattr.

(* For some reason coq has trouble typechecking this if it's inlined *)
Definition make_number (l : list Z) (v : val) : reptype t_number :=
  ((Vint (Int.repr (Zlength l))), v).

Definition cnumber {CS : compspecs} (sh : Share.t) (digit_list : list Z) (p : val) :=
  EX digits : val,
  data_at Ews t_number (make_number digit_list digits) p *
  data_at sh (tarray tulong (Zlength digit_list)) (map Vint (map Int.repr digit_list)) digits.

Definition comparison_int c : val :=
  match c with
  | Lt => Vint (Int.repr (-1))
  | Eq => Vint (Int.repr 0)
  | Gt => Vint (Int.repr 1)
  end.

Definition number_compare_spec : ident * funspec :=
 DECLARE _number_compare
  WITH sh0: share, sh1: share, n0 : val, n1 : val, d0 : list Z, d1 : list Z
  PRE [ tptr t_number, tptr t_number ]
    PROP (readable_share sh0; readable_share sh1)
    PARAMS (n0; n1)
    SEP (cnumber sh0 d0 n0 * cnumber sh1 d1 n1)
  POST [ tint ]
    PROP ()
    RETURN (comparison_int (compare d0 d1))
    SEP (cnumber sh0 d0 n0 * cnumber sh1 d1 n1).

Definition Gprog : funspecs := [ number_compare_spec ].
