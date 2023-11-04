Require Import BinInt List Recdef ZArith Lia.
Import ListNotations.

Local Open Scope list_scope.
Local Open Scope Z_scope.

Compute Z.modulo 7 2.

Search id.
Search (1 < _ -> 0 < _).


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

Example ok0 : 0 <= 153.
Proof.
  lia.
Qed.
Example ok1 : 1 < 10.
Proof.
  lia.
Qed.

Locate eq.
Compute digits 10 153 ok1 ok0.

Theorem digits_cons_inversion : forall h t base n H0 H1, h :: t = digits base n H0 H1 -> h = (Z.modulo n base).
Proof.
  intros h t base n H0 H1. rewrite (digits_equation base n H0 H1).
  remember (n =? 0). destruct b.
  - intros. discriminate H.
  - intros. inversion H. reflexivity.
Qed.

Lemma digits_small_aux : forall digit_list n base H0 H1,
  digit_list = (digits base n H0 H1) ->
  Forall (fun d => -1 < d < base) digit_list.
Proof.
  induction digit_list; intros.
  - apply Forall_nil.
  - apply Forall_cons.
    * rewrite (digits_cons_inversion a digit_list base n H0 H1).
      + split. assert (0 <= n mod base). apply Z_mod_nonneg_nonneg. apply H1. lia. lia.
        apply Z.mod_pos_bound. lia.
      + apply H.
    * rewrite digits_equation in H. destruct (n =? 0). discriminate H. inversion H.
      rewrite <- H4.
      apply (IHdigit_list (n / base) base H0 (Z.div_pos n base H1 (relax_lower_bound H0))).
      apply H4.
Qed.

Theorem digits_small : forall digit_list n base H0 H1,
  digit_list = (digits base n H0 H1) ->
  Forall (fun d => -1 < d < base) digit_list.
Proof.
  apply digits_small_aux.
Qed.
