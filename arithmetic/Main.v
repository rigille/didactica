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

Function digitize (base: Z) (n : Z) (H0: 1 < base) (H1: 0 <= n) {measure Z.abs_nat n} : list Z :=
  if n =? 0 then
    []
  else
    (Z.modulo n base) :: digitize base (Z.div n base) H0 (Z.div_pos n base H1 (relax_lower_bound H0)).
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
Compute digitize 10 153 ok1 ok0.

Theorem digits_cons_inversion_head : forall h t base n H0 H1, h :: t = digitize base n H0 H1 -> h = (Z.modulo n base).
Proof.
  intros h t base n H0 H1. rewrite (digitize_equation base n H0 H1).
  remember (n =? 0). destruct b.
  - intros. discriminate H.
  - intros. inversion H. reflexivity.
Qed.

Theorem digits_cons_inversion_tail : forall h t base n H0 H1,
  h :: t = digitize base n H0 H1 ->
  t = digitize base (Z.div n base) H0 (Z.div_pos n base H1 (relax_lower_bound H0)).
Proof.
  intros h t base n H0 H1. rewrite (digitize_equation base n H0 H1).
  remember (n =? 0). destruct b.
  - intros. discriminate H.
  - intros. inversion H. reflexivity.
Qed.

Lemma digits_small_aux : forall digit_list base n H0 H1,
  digit_list = (digitize base n H0 H1) ->
  Forall (fun d => -1 < d < base) digit_list.
Proof.
  induction digit_list; intros.
  - apply Forall_nil.
  - apply Forall_cons.
    * rewrite (digits_cons_inversion_head a digit_list base n H0 H1).
      + split. assert (0 <= n mod base). apply Z_mod_nonneg_nonneg. apply H1. lia. lia.
        apply Z.mod_pos_bound. lia.
      + apply H.
    * rewrite digitize_equation in H. destruct (n =? 0). discriminate H. inversion H.
      rewrite <- H4.
      apply (IHdigit_list base (n / base) H0 (Z.div_pos n base H1 (relax_lower_bound H0))).
      apply H4.
Qed.

Theorem digits_small : forall base n H0 H1,
  Forall (fun d => -1 < d < base) (digitize base n H0 H1).
Proof.
  intros. remember (digitize base n H0 H1) as digit_list eqn:Hdl.
  apply (digits_small_aux digit_list base n H0 H1 Hdl).
Qed.

Check fold_right.

Definition number (base : Z) (l : list Z) := fold_right (fun h t => h + base*t) 0 l.

Compute number 10 (digitize 10 153 ok1 ok0).
Check digitize.

Theorem number_undoes_digitize : forall base n H0 H1,
  number base (digitize base n H0 H1) = n.
Proof.
  intros; remember (digitize base n H0 H1) as digit_list eqn:Hdigit_list.
  generalize dependent digit_list. intro digit_list. revert H1 H0. generalize n base.
  induction digit_list; intros.
  - simpl. rewrite digitize_equation in Hdigit_list.
    destruct (n0 =? 0) as [condition | condition] eqn:Hcondition.
    apply Z.eqb_eq. apply Hcondition. discriminate Hdigit_list.
  - simpl. rewrite (digits_cons_inversion_head a digit_list base0 n0 H0 H1).
    apply (digits_cons_inversion_tail a digit_list base0 n0 H0 H1) in Hdigit_list.
    rewrite (IHdigit_list (n0 / base0) base0 (Z.div_pos n0 base0 H1 (relax_lower_bound H0)) H0).
    symmetry. rewrite (Z.add_comm (n0 mod base0) (base0 * (n0 / base0))).
    apply (Z_div_mod_eq_full n0 base0). apply Hdigit_list.
    apply Hdigit_list.
Qed.

Definition is_empty {X : Type} (l : list X) : bool :=
  match l with
  | [] => true
  | _  => false
  end.

Search ((?a -> bool) -> (list ?a) -> bool).

Search (bool -> bool -> bool).

Definition clamp (l : list Z) := fold_right (fun h t => if andb (h =? 0) (is_empty t) then [] else h :: t) [] l.

Compute clamp [1; 2; 0; 2; 0; 0].

Lemma bounded_digits_safe_to_digitize : forall digit_list base,
  Forall (fun d => -1 < d < base) digit_list ->
  (0 <= number base digit_list).
Proof.
Admitted.

Theorem digitize_clamps_number (digits : list Z) (base : Z)
  (H0 : 1 < base)
  (H1 : Forall (fun d => -1 < d < base) digits) :
  digitize base (number base digits)
    H0
    (bounded_digits_safe_to_digitize digits base H1)
  =
  (clamp digits).
Proof.
Admitted.


