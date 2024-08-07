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


