Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Didactica.arithmetic.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Definition t_number := Tstruct _number noattr.
