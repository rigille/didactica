From Topology Require Import TopologicalSpaces InteriorsClosures.
From Coq Require Import Logic.Decidable.
From Coq Require Import Logic.Classical_Prop.

Definition Irreducible
  (X : TopologicalSpace)
  (U : Ensemble (point_set X)) :=
  open U /\ forall (A B : Ensemble (point_set X)),
    open A -> open B -> (Included (Intersection A B) U) ->
    (Included A U) \/ (Included B U).

Lemma included_complement: forall {T : Type} (X Y : (Ensemble T)),
  Included X Y <-> Included (Complement Y) (Complement X).
Proof.
  intros. unfold Included, Complement, In, not. split.
  - intros. apply H0.
  apply H. apply H1.
  - intros. destruct (classic (Y x)).
    * apply H1.
    * exfalso. apply (H x H1 H0).
Qed. 

Lemma point_to_irreducible: forall (X : TopologicalSpace) (x : point_set X),
   Irreducible X (Complement (closure (Singleton x))).
Proof.
  unfold Irreducible. intros. split.
  (* First we need to prove that set is open *)
  (* It's open because every closure is closed, and every complement *)
  (* of a closed set is closed *)
  - apply closure_closed.
  - intros. destruct (classic (In A x)).
    * left. unfold Included. intros. unfold Included in H1. 
    apply H1. apply Intersection_intro.
      + apply H3.
      + unfold Intersection, In. apply H3. unfold In, Complement.
    * right.
Admitted.

Lemma open_empty: forall X:TopologicalSpace,
  open (@Empty_set X).
Proof.
intros. destruct X. rewrite <- empty_family_union.
apply open_family_union. intros. destruct H.
Qed.