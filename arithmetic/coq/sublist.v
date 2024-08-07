Require Import BinInt List ZArith Lia.
Import ListNotations.

Local Open Scope list_scope.
Local Open Scope Z_scope.

Require Import VST.zlist.sublist.

Lemma sublist_clamp_high: forall i u (d : list Z),
  Zlength d <= u ->
  sublist i u d = sublist i (Zlength d) d.
Proof.
  intros.
  unfold sublist.
  rewrite firstn_same.
  rewrite firstn_same.
  reflexivity.
  rewrite <- ZtoNat_Zlength. lia.
  rewrite <- ZtoNat_Zlength. lia.
Qed.

Lemma Znth_to_nth: forall i (d : list Z),
  0 <= i ->
  Znth i d = nth (Z.to_nat i) d 0.
Proof.
  intros. unfold Znth. destruct (Z_lt_dec i 0). lia.
  reflexivity.
Qed.

Lemma Znth_over: forall i (d : list Z),
  (Zlength d) <= i ->
  Znth i d = 0.
Proof.
  intros. unfold Znth. destruct (Z_lt_dec i 0).
  remember (Zlength_nonneg d) as H1.
  lia. apply nth_overflow.
  rewrite <- ZtoNat_Zlength.
  lia.
Qed.

Lemma Znth_bounded : forall i base digits,
  1 < base ->
  0 <= i ->
  Forall (fun d : Z => -1 < d < base) digits ->
  -1 < Znth i digits < base.
Proof.
  intros. destruct (Z_lt_dec i (Zlength digits)).
  - apply sublist.Forall_Znth. lia. apply H1.
  - rewrite Znth_over. lia. lia.
Qed.
