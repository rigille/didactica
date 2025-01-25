Require Import Nat.
Require Import Arith.
Require Import Lists.List.
Require Import Lia.
Require Import Coq.Logic.FunctionalExtensionality.

Theorem imagine_if : forall (P : Type),
  (P -> True) -> True.
Proof.
  intros. apply I.
Qed.

Lemma curry_uncurry : forall A B C (f : A -> B -> C),
  curry (uncurry f) = f.
Proof.
  intros. unfold uncurry. unfold curry. reflexivity.
Qed.

Lemma uncurry_curry : forall A B C (f : A * B -> C),
  (eq (uncurry (curry f)) f).
Proof.
  intros.
  apply functional_extensionality. intros.
  compute. destruct x. reflexivity.
Qed.


Definition plus_iter (m n : nat) : nat :=
  iter m S n.

(* We can prove this matches the regular definitions *)
Lemma plus_iter_correct :
  eq plus_iter Nat.add.
Proof.
  apply functional_extensionality; intros m.
  apply functional_extensionality; intros n.
  induction m; simpl.
  - reflexivity.
  - rewrite IHm. reflexivity.
Qed.

Module Exercise_1_2.

Definition equation : (nat -> nat -> nat) -> Type :=
  fun g =>
  (and
    (forall x y, x = y -> g x y = S y)
    (forall x y, x <> y -> g x y = g x (g (pred x) (S y)))).

Definition statement : Type :=
  exists f,
  forall g : nat -> nat -> nat,
  equation g ->
  g = f.

Example example_2_2 : forall g, equation g ->
  (eq
    (g 2 2)
    3).
Proof.
  unfold equation. intros g [H0 H1].
  apply H0. reflexivity.
Qed.

Example example_4_2 : forall g, equation g ->
  (eq
    (g 4 2)
    5).
Proof.
  unfold equation. intros g [H0 H1].
  rewrite (H1 4 2 ltac:(discriminate)). simpl.
  rewrite (H0 3 3 ltac:(reflexivity)). rewrite H0; reflexivity.
Qed.

Example example_5_1 : forall g, equation g ->
  (eq
    (g 5 1)
    6).
Proof.
  intros g.
  intros H.
  assert (equation g) by assumption.
  destruct X.
  rewrite (H1 5 1 ltac:(discriminate)). simpl.
  rewrite (example_4_2 g H).
  rewrite (H0 5 5 ltac:(reflexivity)). reflexivity.
Qed.

Example example_5_3 : forall g, equation g ->
  (eq
    (g 5 3)
    6).
Proof.
  unfold equation. intros g [H0 H1].
  rewrite (H1 5 3 ltac:(discriminate)). simpl.
  rewrite (H0 4 4 ltac:(reflexivity)).
  rewrite (H0 5 5 ltac:(reflexivity)). reflexivity.
Qed.

Example explore : True.
Proof.
  apply (imagine_if {g : nat -> nat -> nat & equation g}); intros [g H].
  unfold equation in H.
  destruct H as [H0 H1].
  generalize (eq_refl (g 5 3)); intros eq.
  rewrite (H1 5 3 ltac:(discriminate)) in eq at 1.
  simpl in eq. rewrite (H0 4 4 ltac:(reflexivity)) in eq.
  rewrite (H0 5 5 ltac:(reflexivity)) in eq.
  apply I.
Qed.

Definition candidate (n m : nat) : nat :=
  S n.

Lemma candidate_fit : equation candidate.
Proof.
  unfold equation. split; intros.
  - unfold candidate. f_equal. exact H.
  - unfold candidate. reflexivity.
Qed.

Lemma independency : forall g, equation g ->
  forall x y,
  g x y = candidate x y.
Proof.
  unfold equation. intros g [H0 H1].
  induction x; intros.
  - induction y.
    + apply (H0 0 0 ltac:(reflexivity)).
    + rewrite (H1 0 (S y) ltac:(discriminate)). simpl.
Abort.

(* f n = f (f (S n)) *)

End Exercise_1_2.

Fixpoint foldn {A} (c : A) (h : A -> A) (n : nat) : A :=
  match n with
  | O => c
  | S pred => h (foldn c h pred)
  end.

Module Exercise_1_4.
  (* 1.4 Express the squaring function sqr : Nat —> Nat in the form
     sqr = (compose f (foldn c h)) for suitable f, c and h. *)
Example exploration : True.
Proof.
  apply (imagine_if
  {A : Type & {f : A -> nat & {c : A & {h : A -> A &
    forall (n : nat),
    Nat.square n = (Basics.compose f (foldn c h)) n}}}}).
  intros [A [f [c [h EQ]]]].
  apply (imagine_if nat). intros n.
  (* generalize (eq 0); intros.
  unfold Nat.square, iter, Basics.compose, nat_rect in H.
  simpl in H. *)
  generalize (EQ O); intros.
  unfold Basics.compose, Nat.square in H.
  simpl in H.
  generalize (EQ (S n)); intros.
  unfold Nat.square, Basics.compose in H0.
  replace ((S n) * (S n)) with (n*n + 2*n + 1) in H0 by lia.
  replace (n * n) with (Nat.square n) in H0 by reflexivity.
  rewrite EQ in H0.
  unfold Basics.compose in H0.
  unfold foldn in H0 at 2.
  fold (@foldn A) in H0.
  apply (imagine_if (eq A (prod nat nat))). intros.
  subst A.
  apply (imagine_if (forall p : nat*nat, f p = fst p)). intros.
  apply (imagine_if (forall p : nat*nat, h p  = ((fst p) + 2*(snd p) + 1, 1 + (snd p)))). intros.
  apply (imagine_if (c = (0, 1))). intros.
  subst c. rewrite (H2 (foldn (0, 1) h n)) in H0.
  rewrite (H1 (fst (foldn (0, 1) h n) + 2 * snd (foldn (0, 1) h n) + 1,
        1 + snd (foldn (0, 1) h n))) in H0.
  unfold fst in H0 at 1.
  unfold snd in H0.
  apply I.
Qed.

Definition square_foldn_aux (p : nat * nat) :=
  ((fst p) + 2*(snd p) + 1, S (snd p)).

Theorem square_foldn :
  Nat.square = (Basics.compose fst (foldn (0, 0) square_foldn_aux)).
Proof.
  apply functional_extensionality.
  assert (forall n, snd ((foldn (0, 0) square_foldn_aux) n) = n).
  - induction n.
    + reflexivity.
    + simpl. rewrite IHn. reflexivity.
  - intros n. induction n.
    + reflexivity.
    + unfold Nat.square, Basics.compose.
      replace ((S n) * (S n)) with (n*n + 2*n + 1) by lia.
      replace (n * n) with (Nat.square n) by reflexivity.
      replace (2 * n) with
        (2 * (snd (foldn (0, 0) square_foldn_aux n))).
      rewrite IHn. reflexivity. rewrite H. reflexivity.
Qed.

End Exercise_1_4.

(* mult m = foldn(0, plus m) becomes: *)
Definition mult_iter (m : nat) : nat -> nat :=
  fun n => iter n (plus_iter m) 0.

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
