Require Import BinInt List ZArith.
Import ListNotations.

Local Open Scope list_scope.
Local Open Scope Z_scope.

Definition push := true.
Definition pop := false.

Fixpoint associate_inner
  (ops : list bool)
  (terms : list Z)
  (top : Z)
  (stack : list Z) : Z :=
  match ops with
  | [] => top
  | hop :: opt =>
    match hop with
    | true =>
      match terms with
      | [] => top
      | n :: terms' =>
        associate_inner opt terms' n (top :: stack)
      end
    | false =>
      match stack with
      | [] => top
      | sh :: st =>
        associate_inner opt terms (sh + top) st
      end
    end
  end.

Definition associate (ops : list bool) (terms : list Z) :=
  associate_inner ops terms 0 [].

Example associate_test0 :
  forall x y z : Z,
  (eq
    (associate
      [true; false; true; false; true; false]
      [x; y; z])
    ((x + y) + z)).
Proof.
  intros. unfold associate, associate_inner. simpl.
  reflexivity.
Qed.

Example associate_test1 :
  forall x y z : Z,
  (eq
    (associate
      [true; true; true; false; false; false]
      [x; y; z])
    (x + (y + z))).
Proof.
  intros. unfold associate, associate_inner. simpl.
  reflexivity.
Qed.

Fixpoint list_eqb (l1 l2 : list bool) : bool :=
  match l1, l2 with
  | [], [] => true
  | x1 :: xs1, x2 :: xs2 => (Bool.eqb x1 x2) && (list_eqb xs1 xs2)
  | _, _ => false
  end.
