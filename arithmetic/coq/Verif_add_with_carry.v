Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.

Require Import Didactica.arithmetic.
Require Import Didactica.Add.
Require Import Didactica.number.

Lemma body_add_with_carry : semax_body Vprog Gprog f_add_with_carry add_with_carry_spec.
Proof.
  start_function.
  unfold digit_bound in *.
  forward. deadvars!. normalize.
(*
  replace
    (Int64.repr (left_digit + Z.b2z carry_in))
  with
    (Int64.repr
      (Z.modulo
        (left_digit + Z.b2z carry_in)
        Int64.max_unsigned)).
  admit.
  Search (@eq int _ _).
  Check eq.

  unfold Int64.repr.
  replace
    (Int64.Z_mod_modulus
      ((left_digit + Z.b2z carry_in) mod Int64.max_unsigned))
  with
    (((left_digit + Z.b2z carry_in) mod Int64.max_unsigned) mod Int64.max_unsigned).
  reflexiv
  rewrite Int64.Z_mod_modulus_eq.
  Search Int64.Z_mod_modulus.

  Search Int64.repr.
  forward. normalize.
  forward.
  replace
    (Int64.ltu
      (Int64.repr (left_digit + Z.b2z carry_in))
      (Int64.repr (Z.b2z carry_in)))
  with
    (Z.ltb
      (Z.modulo (Z.b2z carry_in + left_digit) Int64.max_unsigned)
      (Z.b2z carry_in)). admit.
  normalize.
  entailer!. forward.
  *)
Admitted.
