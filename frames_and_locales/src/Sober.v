From Topology Require Import TopologicalSpaces.

Lemma open_empty: forall X:TopologicalSpace,
  open (@Empty_set X).
Proof.
intros. destruct X. rewrite <- empty_family_union.
apply open_family_union. intros. destruct H.
Qed.