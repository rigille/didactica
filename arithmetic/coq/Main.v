Require Import BinInt List Recdef ZArith Lia ProofIrrelevance.
Import ListNotations.

Local Open Scope list_scope.
Local Open Scope Z_scope.


Lemma relax_lower_bound {a : Z} (H : 1 < a) : (0 < a).
Proof. lia. Qed.

Function digitize (base: Z)
                  (n : Z)
                  (H0: 1 < base)
                  (H1: 0 <= n)
                  {measure Z.abs_nat n}
         : list Z :=
  if n =? 0 then
    []
  else
    (Z.modulo n base)
    :: digitize base (Z.div n base)
                H0
                (Z.div_pos n base H1 (relax_lower_bound H0)).
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

Theorem digits_cons_inversion_head : forall
  h t base n H0 H1,
  h :: t = digitize base n H0 H1 ->
  h = (Z.modulo n base).
Proof.
  intros h t base n H0 H1. rewrite (digitize_equation base n H0 H1).
  remember (n =? 0). destruct b.
  - intros. discriminate H.
  - intros. inversion H. reflexivity.
Qed.

Theorem digits_cons_inversion_tail : forall h t base n H0 H1,
  h :: t = digitize base n H0 H1 ->
  t = digitize base (Z.div n base)
               H0 (Z.div_pos n base H1 (relax_lower_bound H0)).
Proof.
  intros h t base n H0 H1. rewrite (digitize_equation base n H0 H1).
  remember (n =? 0). destruct b.
  - intros. discriminate H.
  - intros. inversion H. reflexivity.
Qed.

Lemma digits_small_aux : forall digits base n H0 H1,
  digits = (digitize base n H0 H1) ->
  Forall (fun d => -1 < d < base) digits.
Proof.
  induction digits; intros.
  - apply Forall_nil.
  - apply Forall_cons.
    * rewrite (digits_cons_inversion_head a digits base n H0 H1).
      + split. assert (0 <= n mod base). apply Z_mod_nonneg_nonneg.
        apply H1. lia. lia.
        apply Z.mod_pos_bound. lia.
      + apply H.
    * rewrite digitize_equation in H. destruct (n =? 0).
      discriminate H. inversion H.
      rewrite <- H4.
      apply (IHdigits base (n / base) H0
                      (Z.div_pos n base H1 (relax_lower_bound H0))).
      apply H4.
Qed.

Theorem digits_small : forall base n H0 H1,
  Forall (fun d => -1 < d < base) (digitize base n H0 H1).
Proof.
  intros. remember (digitize base n H0 H1) as digits eqn:Hdl.
  apply (digits_small_aux digits base n H0 H1 Hdl).
Qed.

Definition number (base : Z) (l : list Z) :=
  fold_right (fun h t => t*base + h) 0 l.

Theorem number_undoes_digitize : forall base n H0 H1,
  number base (digitize base n H0 H1) = n.
Proof.
  intros; remember (digitize base n H0 H1) as digits eqn:Hdigit_list.
  generalize dependent digits. intro digits. revert H1 H0.
  generalize n base.
  induction digits; intros.
  - simpl. rewrite digitize_equation in Hdigit_list.
    destruct (n0 =? 0) as [condition | condition] eqn:Hcondition.
    apply Z.eqb_eq. apply Hcondition. discriminate Hdigit_list.
  - simpl. rewrite
    (digits_cons_inversion_head a digits base0 n0 H0 H1).
    apply
    (digits_cons_inversion_tail a digits base0 n0 H0 H1) in Hdigit_list.
    rewrite (IHdigits (n0 / base0) base0
                      (Z.div_pos n0 base0 H1 (relax_lower_bound H0)) H0).
    symmetry.
    rewrite (Z.mul_comm (n0 / base0) base0).
    apply (Z_div_mod_eq_full n0 base0). apply Hdigit_list.
    apply Hdigit_list.
Qed.

Definition is_empty {X : Type} (l : list X) : bool :=
  match l with
  | [] => true
  | _  => false
  end.

Theorem is_empty_spec : forall {X} (l : list X),
   Bool.reflect (eq l nil) (is_empty l).
Proof.
  intros. destruct l.
  - apply Bool.ReflectT. reflexivity.
  - apply Bool.ReflectF. discriminate.
Qed.

(* Search ((?a -> bool) -> (list ?a) -> bool). *)

(* Search (bool -> bool -> bool). *)

(* Search (Type -> Type -> Type). *)
(* Print prod. *)

Definition clamp (l : list Z) :=
  fold_right (fun h t =>
               if andb (h =? 0) (is_empty t) then
                 []
               else
                 h :: t)
             [] l.

Lemma bounded_digits_safe_to_digitize : forall digits base,
  Forall (fun d => -1 < d < base) digits ->
  (0 <= number base digits).
Proof.
  induction digits; intros.
  - simpl. lia.
  - simpl. inversion H. destruct H2. assert (0 <= number base digits).
    apply IHdigits. apply H3. assert (0 <= a) by lia.
    assert (0 <= base) by lia.
    assert (0 <= base * (number base digits)).
    apply Z.mul_nonneg_nonneg.
    apply H7. apply H5.
    lia.
Qed.

Lemma number_zero_digits_zero : forall digits base,
  1 < base ->
  Forall (fun d => -1 < d < base) digits ->
  0 = number base digits <->
  Forall (fun d => d = 0) digits.
Proof.
  induction digits; intros.
  - split; intros. apply Forall_nil.
    reflexivity.
  - split.
    + simpl; intros.
      inversion H0; subst.
      assert (0 = number base digits) by nia.
      rewrite <- H2 in H1. simpl in H1.
      rewrite -> IHdigits in H2; try assumption.
      apply Forall_cons. symmetry. apply H1. assumption.
    + intros. inversion H1; subst.
      simpl. assert (0 = number base digits).
      rewrite IHdigits. apply H5.
      assumption. inversion H0; subst; assumption.
      lia.
Qed.

Lemma clamp_all_zeros : forall digits,
  Forall (fun d => d = 0) digits <->
  clamp digits = [].
Proof.
  split.
  - intros. induction H.
    + reflexivity.
    + simpl. rewrite IHForall. rewrite H. reflexivity.
  - intros. induction digits.
    + apply Forall_nil.
    + apply Forall_cons.
      * simpl in H. destruct (andb (a =? 0) (is_empty (clamp digits)))
        as [condition | condition] eqn:Hcondition.
        apply andb_prop in Hcondition. destruct Hcondition.
        apply Z.eqb_eq. apply H0.
        discriminate H.
      (* this could be simpler but I'm lazy *)
      * apply IHdigits. simpl in H.
        destruct (andb (a =? 0) (is_empty (clamp digits)))
        as [condition | condition] eqn:Hcondition.
        apply andb_prop in Hcondition. destruct Hcondition.
        destruct (is_empty_spec (clamp digits)). apply e.
        discriminate H1. discriminate H.
Qed.

Theorem digitize_clamps_number (digits : list Z) (base : Z)
  (H0 : 1 < base)
  (H1 : Forall (fun d => -1 < d < base) digits) :
  (eq (digitize base
                (number base digits)
                H0
                (bounded_digits_safe_to_digitize digits base H1))
      (clamp digits)).
Proof.
  remember (bounded_digits_safe_to_digitize digits base H1) as H1'.
  generalize H0 H1 H1'.
  induction digits.
  - reflexivity.
  - intros. rewrite digitize_equation.
    (* Search (Bool.reflect (_ = _) (_ =? _)). *)
    destruct (Z.eqb_spec (number base (a :: digits)) 0).
    + symmetry in e.
      apply (number_zero_digits_zero (a :: digits) base H2 H3) in e.
      symmetry. rewrite <- clamp_all_zeros. apply e.
    + simpl.
      inversion H1.
      remember (Z.div_pos (number base digits * base + a) base H1'0
        (relax_lower_bound H2)) as H1''.
      generalize H1'' as H1'''.
      rewrite (Z.add_comm ((number base digits) * base) a).
      rewrite Z_mod_plus_full.
      assert (base > 0) by lia.
      rewrite (Z_div_plus a (number base digits) base H7).
      assert (0 <= a < base) by lia. rewrite (Z.div_small a base H8).
      simpl. (* Search (?a mod ?b = ?a). *) rewrite (Z.mod_small a base H8).
      intros. rewrite (IHdigits H6 H1''').
        * destruct (is_empty_spec (clamp digits)).
          { simpl in n.
            destruct (Z.eqb_spec a 0).
            { apply clamp_all_zeros in e.
              rewrite <- (number_zero_digits_zero digits base H0 H6)
              in e.
              rewrite <- e in n.
              rewrite -> e0 in n.
              simpl in n. exfalso. apply n. reflexivity. }
            { reflexivity.  } }
          { rewrite Bool.andb_false_r. reflexivity. }
        * apply proof_irrelevance.
        * apply H6.
Qed.

Lemma compare_div_mod_lt : forall base q0 q1 r0 r1,
  1 < base ->
  0 <= r0 < base ->
  0 <= r1 < base ->
  base*q0 + r0 < base*q1 + r1 <-> (q0 < q1 \/ ((q0 = q1) /\ r0 < r1)).
Proof.
  nia.
Qed.

Lemma compare_div_mod_gt : forall base q0 q1 r0 r1,
  1 < base ->
  0 <= r0 < base ->
  0 <= r1 < base ->
  base*q0 + r0 > base*q1 + r1 <-> (q0 > q1 \/ ((q0 = q1) /\ r0 > r1)).
Proof.
  nia.
Qed.

Lemma compare_div_mod_eq : forall base q0 q1 r0 r1,
  1 < base ->
  0 <= r0 < base ->
  0 <= r1 < base ->
  base*q0 + r0 = base*q1 + r1 <-> (q0 = q1 /\ r0 = r1).
Proof.
  intros; split; intros.
  - apply (Z.div_mod_unique base).
    + left. apply H0.
    + left. apply H1.
    + apply H2.
  - destruct H2. rewrite H2. rewrite H3.
    reflexivity.
Qed.

Definition product_compare c0 c1 :=
  match c0 with
  | Gt => Gt
  | Lt => Lt
  | Eq => c1
  end.

Lemma compare_div_mod : forall base q0 q1 r0 r1,
  1 < base ->
  0 <= r0 < base ->
  0 <= r1 < base ->
  (eq (Z.compare (base*q0 + r0) (base*q1 + r1))
      (product_compare (Z.compare q0 q1) (Z.compare r0 r1))).
Proof.
  intros.
  destruct (base * q0 + r0 ?= base * q1 + r1) eqn:EqCmp.
  - apply Z.compare_eq in EqCmp.
    rewrite compare_div_mod_eq in EqCmp; try lia.
    destruct EqCmp. subst.
    rewrite Z.compare_refl. rewrite Z.compare_refl.
    reflexivity.
  - rewrite Z.compare_lt_iff in EqCmp.
    rewrite compare_div_mod_lt in EqCmp; try lia.
    destruct EqCmp.
    + rewrite <- Z.compare_lt_iff in H2.
      rewrite H2. reflexivity.
    + destruct H2. subst. rewrite Z.compare_refl.
      rewrite <- Z.compare_lt_iff in H3.
      rewrite H3. reflexivity.
  - rewrite Z.compare_gt_iff in EqCmp.
    rewrite compare_div_mod_lt in EqCmp; try lia.
    destruct EqCmp.
    + rewrite Z.compare_antisym. rewrite <- Z.compare_lt_iff in H2.
      rewrite H2. reflexivity.
    + destruct H2; subst.
      rewrite Z.compare_refl. rewrite Z.compare_antisym.
      rewrite <- Z.compare_lt_iff in H3.
      rewrite H3. reflexivity.
Qed.

Fixpoint compare (l0 l1 : list Z) :=
  match l0 with
  | [] =>
    if forallb (fun n => 0 =? n) l1 then
      Eq
    else
      Lt
  | h0 :: t0 =>
    match l1 with
    | [] =>
      if forallb (fun n => 0 =? n) (h0 :: t0) then
        Eq
      else
        Gt
    | h1 :: t1 =>
      product_compare (compare t0 t1) (Z.compare h0 h1)
    end
  end.

(* TODO move this to a list library *)
Theorem Forall_forallb : forall
  {X : Type} (p : X -> Prop) (f : X -> bool) (l : list X),
  (forall x, p x <-> (true = f x)) ->
  ((Forall p l) <->
  (true = forallb f l)).
Proof.
  intros. split; induction l; intros.
  - reflexivity.
  - inversion H0.
    simpl. rewrite -> (H a) in H3.
    rewrite <- H3.
    rewrite <- IHl. reflexivity.
    apply H4.
  - apply Forall_nil.
  - 
    simpl in H0.
    apply Bool.andb_true_eq in H0.
    destruct H0.
    apply Forall_cons.
    rewrite H.
    apply H0. apply IHl.
    apply H1.
Qed.

Lemma compare_antisym : forall digits0 digits1,
  (compare digits0 digits1) = CompOpp (compare digits1 digits0).
Proof.
  induction digits0; intros.
  - destruct digits1.
    + reflexivity.
    + unfold compare.
      destruct (forallb (fun n : Z => 0 =? n) (z :: digits1));
      reflexivity.
  - destruct digits1; unfold compare.
    + destruct (forallb (fun n : Z => 0 =? n) (a :: digits0));
      reflexivity.
    + fold compare.
      rewrite (IHdigits0 digits1).
      destruct (compare digits1 digits0); simpl.
      * apply Z.compare_antisym.
      * reflexivity.
      * reflexivity.
Qed.

Lemma compare_empty : forall base digits,
  (1 < base) ->
  (Forall (fun d => -1 < d < base) digits) ->
  (eq (compare [] digits)
      (Z.compare 0 (number base digits))).
Proof.
  intros.
  unfold compare. replace (number base []) with 0 by reflexivity.
  remember (forallb (fun n : Z => 0 =? n) digits) as all_zeros.
  destruct all_zeros.
  + rewrite <- (Forall_forallb (fun d => d = 0)
                               (fun n => 0 =? n))
    in Heqall_zeros.
    rewrite <- (number_zero_digits_zero digits base) in Heqall_zeros.
    rewrite <- Heqall_zeros.
    reflexivity.
    apply H.
    apply H0.
    lia.
  + assert (number base digits <= 0 \/ 0 < number base digits)
    by lia.
    destruct H1.
    * assert (0 <= number base digits).
      apply bounded_digits_safe_to_digitize.
      apply H0.
      assert (0 = number base digits) by lia.
      rewrite number_zero_digits_zero in H3.
      rewrite (Forall_forallb (fun d => d = 0)
                    (fun n => 0 =? n)) in H3.
      rewrite <- Heqall_zeros in H3.
      discriminate H3.
      lia.
      apply H.
      apply H0.
    * symmetry. rewrite Z.compare_lt_iff.
      apply H1.
Qed.

Theorem compare_correct : forall base digits0 digits1,
  (1 < base) ->
  (Forall (fun d => -1 < d < base) digits0) ->
  (Forall (fun d => -1 < d < base) digits1) ->
  (eq (compare digits0 digits1)
      (Z.compare (number base digits0) (number base digits1))).
Proof.
  induction digits0 as [ | hdigits0 tdigits0] ; intros.
  - apply compare_empty. apply H.
    apply H1.
  - destruct digits1 as [ | hdigits1 tdigits1].
    + rewrite compare_antisym.
      rewrite (compare_empty base (hdigits0 :: tdigits0)).
      rewrite <- Z.compare_antisym.
      reflexivity. apply H. apply H0.
    + unfold compare; fold compare.
      unfold number; simpl.
      replace (fold_right (fun h t : Z => t * base + h) 0 tdigits0)
      with (number base tdigits0)
      by reflexivity.
      replace (fold_right (fun h t : Z => t * base + h) 0 tdigits1)
      with (number base tdigits1)
      by reflexivity.
      (* Search (_*_ = _*_). *)
      rewrite (Z.mul_comm (number base tdigits0) base).
      rewrite (Z.mul_comm (number base tdigits1) base).
      rewrite (compare_div_mod base
                              (number base tdigits0)
                              (number base tdigits1)
                              hdigits0
                              hdigits1); try assumption.
      inversion H0. inversion H1.
      rewrite IHtdigits0; try assumption; reflexivity.
      inversion H0; lia. inversion H1; lia.
Qed.
