Require Import Nat.
Require Import Arith.
Require Import Lists.List.
Import ListNotations.

Lemma curry_uncurry : forall A B C (f : A -> B -> C),
  curry (uncurry f) = f.
Proof.
  intros. unfold uncurry. unfold curry. reflexivity.
Qed.

Check nat_rect.

Compute Nat.iter 0 (Nat.add 2) 4.

Lemma uncurry_curry : forall A B C (f : A * B -> C),
  uncurry (curry f) = f.
Proof.
Admitted.

(* First, plus m = foldn(m, succ) can be written as: *)
Definition plus_iter (m : nat) : nat -> nat :=
  fun n => iter m S n.

(* mult m = foldn(0, plus m) becomes: *)
Definition mult_iter (m : nat) : nat -> nat :=
  fun n => iter n (plus_iter m) 0.

(* We can prove these match the regular definitions *)
Lemma plus_iter_correct m n :
  plus_iter m n = m + n.
Proof.
  unfold plus_iter.
  induction m; simpl.
  - reflexivity.
  - rewrite IHm. reflexivity.
Qed.

Fixpoint variadic (X Y : Type) (n : nat) : Type :=
  match n with
  | O => Y
  | S pred => X -> (variadic X Y pred)
  end.

Fixpoint multi_cons_aux {X : Type} (n : nat) (acc : list X) : variadic X (list X) n :=
  match n return variadic X (list X) n with
  | O => rev acc
  | S pred => fun x => (multi_cons_aux pred (cons x acc))
  end.

Definition multi_cons {X : Type} (n : nat) :=
  @multi_cons_aux X n [].

Compute multi_cons 3 true false false.

(* For factorial, we can use a similar pair approach *)
Definition fact_step (p : nat * nat) : nat * nat :=
  let (m, n) := p in (m + 1, (m + 1) * n).

Definition factorial (n : nat) : nat :=
  snd (iter n fact_step (0, 1)).
