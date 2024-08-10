Require Import BinInt List ZArith.
Require Import Lia.
Import ListNotations.

Local Open Scope list_scope.
Local Open Scope Z_scope.

Definition unused (X : Prop) (Y : Type) :=
  sum (X -> False) Y.

Definition lift {X : Prop} {Y: Type} (t : unused X Y) : X -> Y :=
  fun x =>
    match t with
    | inl contradiction => False_rect Y (contradiction x)
    | inr value => value
    end.

Theorem unused_does_not_matter : forall X Y (pre_value : unused X Y) (x x': X),
  (eq (lift pre_value x) (lift pre_value x')).
Proof.
  intros.
  destruct pre_value.
  - exfalso. apply (f x).
  - reflexivity.
Qed.


Definition push := true.
Definition pop := false.

Inductive tree : Type :=
  | Tip
  | Node (left : tree) (right : tree).

Fixpoint size (t : tree) : nat :=
  match t with
  | Tip => 1
  | Node l r => (size l) + (size r)
  end.


Theorem one_not_zero : (le 1 0) -> False.
Proof.
  intros. lia.
Qed.

Theorem slack_left : forall i j k, ((le i k) -> False) -> ((le (i + j) k) -> False).
Proof.
  intros. lia.
Qed.

Theorem slack_right : forall i j k, ((le j k) -> False) -> ((le (i + j) k) -> False).
Proof.
  intros. lia.
Qed.

Fixpoint associate_aux (ops : tree) (terms : list Z) : Z * (list Z) :=
  match ops with
  | Tip =>
      match terms with
      | [] => (0, [])
      | h :: t => (h, t)
      end
  | Node l r =>
      let (sl, terms') := associate_aux l terms in
      let (sr, terms'') := associate_aux r terms' in
      (sl + sr, terms'')
  end.

Definition associate (ops : tree) (terms : list Z) :=
  (fst (associate_aux ops terms)).

Example associate_test0 :
  forall x y z : Z,
  (eq
    (associate
      (Node (Node Tip Tip) Tip)
      [x; y; z])
    ((x + y) + z)).
Proof.
  reflexivity.
Qed.

Example associate_test1 :
  forall x y z : Z,
  (eq
    (associate
      (Node Tip (Node Tip Tip))
      [x; y; z])
    (x + (y + z))).
Proof.
  reflexivity.
Qed.

Definition add (a b : tree * list Z) : tree * list Z :=
  (Node (fst a) (fst b), (snd a) ++ (snd b)).

Definition wrap (a : Z) : tree * list Z := (Tip, [a]).

Theorem associate_correctness : forall (a b : tree) (t : list Z),
  if (Nat.eqb (size a) (size b)) then
    associate a t = associate b t
  else
    True.
Proof.
Admitted.

Theorem scary_association : forall a b c d e f g,
  (eq
    ((((a + b) + (c + d)) + e) + (f + g))
    ((((a + (b + c) + d) + e) + f) + g)).
Proof.
  intros.
  apply
    (associate_correctness
      (Node (Node (Node (Node Tip Tip) (Node Tip Tip)) Tip) (Node Tip Tip))
      (Node (Node (Node (Node (Node Tip (Node Tip Tip)) Tip) Tip) Tip) Tip)
      [a; b; c; d; e; f; g]).
Qed.



