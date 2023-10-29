Require Import BinInt List Recdef ZArith Lia.
Import ListNotations.

Local Open Scope list_scope.
Local Open Scope Z_scope.

Compute Z.modulo 7 2.

Search id.
Search (_ / _ < _).


Lemma relax_lower_bound {a : Z} (H : 1 < a) : (0 < a).
Proof. lia. Qed.

Check Z.div_pos.

Function digits (base: Z) (n : Z) (H0: 1 < base) (H1: 0 <= n) {measure Z.abs_nat n} : list Z :=
  if n =? 0 then
    []
  else
    (Z.modulo n base) :: digits base (Z.div n base) H0 (Z.div_pos n base H1 (relax_lower_bound H0)).
Proof.
  intros. apply (Zabs2Nat.inj_lt (n / base) n ). 
  - apply (Z.div_pos n base). apply H1. lia.
  - apply H1.
  - apply (Z.div_lt n base). lia. apply H0.
Defined.

Print eq.

Example ok0 : 0 <= 153.
Proof.
  lia.
Qed.
Example ok1 : 1 < 10.
Proof.
  lia.
Qed.

Compute digits 10 153 ok1 ok0.
