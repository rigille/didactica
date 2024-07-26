Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Didactica.arithmetic.
Require Import Didactica.number.

Lemma body_number_add_inner: semax_body Vprog Gprog f_number_add_inner number_add_inner_spec.
Proof.
  start_function.
  forward. forward. unfold make_number. forward_call.
  forward. forward.
Admitted.
