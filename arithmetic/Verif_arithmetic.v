Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Didactica.Main.
Require Import Didactica.arithmetic.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Definition t_number := Tstruct _number noattr.

Definition cdigits {CS : compspecs} (sh : Share.t) (digits : list Z) (p : val) : mpred :=
  data_at sh (tarray tulong (Zlength digits)) (map Vint (map Int.repr digits)) p.

Definition comparison_int c : val :=
  match c with
  | Lt => Vint (Int.repr (-1))
  | Eq => Vint (Int.repr 0)
  | Gt => Vint (Int.repr 1)
  end.

Definition number_compare_spec : ident * funspec :=
 DECLARE _number_compare
  WITH sh0: share, sh1: share, n0 : val, s0: val, dp0 : val, d0 : list Z,
       n1 : val, s1 : val, dp1 : val, d1 : list Z
  PRE [ tptr t_number, tptr t_number ]
    PROP (readable_share sh0; readable_share sh1)
    PARAMS (n0; n1)
    SEP (
      data_at Ews t_number ((Vint (Int.repr (Zlength d0))), s0) dp0;
      (cdigits sh0 d0 dp0);
      data_at Ews t_number ((Vint (Int.repr (Zlength d1))), s1) dp1;
      (cdigits sh1 d1 dp1))
  POST [ tint ]
    PROP ()
    RETURN (comparison_int (compare d0 d1))
    SEP (
      data_at Ews t_number ((Vint (Int.repr (Zlength d0))), s0) dp0;
      (cdigits sh0 d0 dp0);
      data_at Ews t_number ((Vint (Int.repr (Zlength d1))), s1) dp1;
      (cdigits sh1 d1 dp1)).

Definition cnumber (CS : compspecs) (sh : Share.t) (digits : list Z) (s : val) (dp : val) :=
  data_at Ews t_number (Vint (Int.repr (Zlength digits)), s) dp.

Definition Gprog : funspecs := [ number_compare_spec ].
