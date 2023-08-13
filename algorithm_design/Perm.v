From Coq Require Import Bool List Permutation Nat Datatypes PeanoNat.
Import ListNotations.

Fixpoint insert {X : Type} (pos : nat) (x : X) (l : list X) : list X :=
  match pos with
  | O => x :: l
  | S pred => match l with
              | h :: t => h :: insert pred x t
              | [] => [x]
              end
  end.

Fixpoint permute {X : Type} (swaps : list nat) (l : list X) : list X :=
  match swaps with
  | [] => l
  | n :: swaps' => match l with
                   | [] => []
                   | h :: t => insert n h (permute swaps' t)
                   end
  end.

Search (list ?a -> list ?a -> list ?a).

Theorem permute_split : forall X n s (l : list X),
  permute s l =
  permute (firstn n s)
          (app (firstn n l)
               (permute (skipn n s)
                        (skipn n l))).
Proof.
  induction n; intros.
  - simpl. reflexivity.
  - simpl. destruct s; destruct l; simpl.
    + reflexivity.
    + rewrite firstn_skipn. reflexivity.
    + destruct (skipn n s); reflexivity.
    + rewrite <- IHn. reflexivity.
Qed.

Theorem firstn_app : forall X (n : nat) (a b : list X),
  le (length a) n ->
  firstn n (app a b)
  =
  (app a
       (firstn (sub n (length a))
               b)).
Proof.
Admitted.

Theorem firstn_append_cons : forall X (x : X) (a b : list X),
  firstn (S (length a)) (a ++ x :: b) = a ++ [x].
Proof.
  intros. Search (sub (S _) _).
  rewrite firstn_app. 
  - rewrite -> (Nat.sub_succ_l _ _ (le_n (length a))).
    rewrite -> Nat.sub_diag. simpl. reflexivity.
  - apply le_S. apply le_n.
Qed.

(* firstn_all *)

Search (firstn (length ?a) ?a).

Check firstn_length_le.
(* firstn_length_le *)

Search firstn.

Theorem insert_not_empty : forall X pos (x : X) l, ~ ([] = insert pos x l).
Proof.
  intros. destruct pos; destruct l; discriminate.
Qed.

Theorem insert_spec : forall X pos (x : X) l,
    (insert pos x l) = (firstn pos l) ++ [x] ++ (skipn pos l).
Proof.
  Search (nat -> list _ -> list _). intros.
  - induction pos.
    * reflexivity.
    * simpl. induction l.
      + reflexivity.
      + fold firstn in IHl. admit.
Admitted.

Definition insert_to_permute (f : nat -> list nat -> list nat) := 
 forall (X : Type) (i : nat) (s : list nat) (h : X) (t : list X),
   insert i h (permute s t) = permute (f i s) (h :: t).

Theorem permute_cons_O_right : forall X i s0 s1 s' h (t : list X),
  permute s0 (permute s1 t) = permute s' t ->
  permute (i :: s0) (permute (O :: s1) (h :: t)) =
  permute (i :: s') (h :: t).
Proof.
  intros. simpl. rewrite H. reflexivity.
Qed.

Fixpoint valid_swaps (s : list nat) (n : nat) : Prop :=
  match s with
  | [] => True
  | sh :: st => sh <= n /\ match n with (* TODO: better way to write this? *)
                           | O => False
                           | S pred => (valid_swaps st pred)
                           end
  end.

Theorem two_swaps_le : forall X (n n' : nat) (h h' : X) (l : list X),
  n <= n' ->
  insert n h (insert n' h' l) =
  (firstn n l) ++ h :: (firstn (sub n' n) (skipn n l)) ++ h' :: (skipn n' l).
Proof.
Admitted.

Theorem two_swaps_le_S : forall X (n n' : nat) (h h' : X) (l : list X),
  n' > n ->
  insert n' h' (insert n h l) =
  (firstn n l) ++ h :: (firstn (sub (pred n') n) (skipn n l)) ++ h' :: (skipn (pred n') l).
Proof.
Admitted.

Theorem swap_inserts_gt : forall X (n n' : nat) (h h' : X) (l : list X),
  n' > n ->
  insert n' h' (insert n h l) = insert n h (insert (pred n') h' l).
Proof.
  intros.
  rewrite two_swaps_le_S.
  - rewrite two_swaps_le.
    + reflexivity.
    + apply Nat.lt_le_pred. apply H.
  - apply H.
Qed.

Theorem swap_inserts_le : forall X (n n' : nat) (h h' : X) (l : list X),
  n' <= n ->
  insert n' h' (insert n h l) = insert (S n) h (insert n' h' l).
Proof.
  intros. symmetry. apply swap_inserts_gt. Search (_ <= _ -> _ < S _).
  apply Arith_prebase.le_lt_n_Sm. apply H.
Qed.

Fixpoint equivalent_insert (s : list nat) (n : nat) : list nat * nat :=
  match s with
  | [] => ([], n)
  | sh :: st => let (st', n') := equivalent_insert st (pred n) in
                if sh <=? n' then
                  (sh :: st', (S n'))
                else
                  ((pred sh) :: st', n')
  end.
(*
permute (a :: b :: []) (x :: y :: h :: [])
insert a x (insert b y (insert 0 h []))
*)
Theorem valid_swaps_not_empty : forall X a s (l : list X),
valid_swaps (a :: s) (length l) ->
~ [] = l.
Proof.
  destruct l; simpl; intros; destruct H as [H1 H2].
  - exfalso. apply H2.
  - discriminate.
Qed.

Theorem equivalent_insert_spec : forall X (s s': list nat) (n n': nat) (h : X) (l : list X),
  valid_swaps s (length l) ->
  le (length s) n ->
  le n (length l) ->
  (s', n') = equivalent_insert s n ->
  permute s (insert n h l) = insert n' h (permute s' l).
Proof.
  induction n; intros.
  - inversion H0. destruct s; try discriminate.
    simpl in H2. injection H2; intros. 
    rewrite H5. rewrite H3. reflexivity.
  - destruct l. inversion H1. destruct s.
    * simpl. injection H2; intros.
      rewrite H3. rewrite H4. reflexivity.
    * simpl. simpl in H2. rewrite IHn with n h l.  destruct (Nat.leb_spec n0 n').
      +
(*  intros. induction s.
  - reflexivity.
  - simpl. remember (equivalent_insert s (pred n)) as ei.
    destruct ei as [st'' n''].
    destruct (Nat.leb_spec0 a n'').
    + remember (insert n h l) as inhl.
      destruct inhl as [|ilh ilt].
       * exfalso. apply (insert_not_empty X n h l).
         apply Heqinhl.
       * simpl. destruct l.
       simpl in H.
       Search (reflect (_ <= _) _). Nat.le_spec. *)
(* (firstn n l) ++ h :: (firstn (sub n' n) (skipn n l)) ++ h' :: (skip n' l) *)

(*
permute s (permute (sh :: st) (h :: t))

let pt = permute st t
permute s ((firstn sh pt) ++ h :: (skipn sh pt))

let pt = permute st t
let inserted = ((firstn sh pt) ++ h :: (skipn sh pt))
permute (firstn sh s)
        (app (firstn inserted)
             (permute (skipn sh s)
                      (skipn sh inserted)))

let pt = permute st t
permute (firstn sh s)
        (app (firstn sh pt)
             (permute (skipn sh s)
                      (h :: (skipn sh pt))))

* caso skipn sh s = []

let pt = permute st t
permute s (insert sh h pt)

* caso skipn sh s = (ssh :: sst)

let pt = permute st t
let (ssh, sst) = skipn sh s
permute (firstn sh s)
        (app (firstn sh pt)
             (permute (ssh :: sst)
                      (h :: (skipn sh pt))))

let pt = permute st t
let (ssh, sst) = skipn sh s
permute (firstn sh s)
        (insert (ssh + sh)
                h
                (app (firstn sh pt)
                     (permute sst (skipn sh pt))))



permute s (insert n h l) = insert (equivalent_insert s n) h (permute s l).
*)

Fixpoint inserts {X : Type} (x : X) (l s : list X) : Prop :=
  (s = List.cons x l) \/
  match l with
  | List.nil => True
  | List.cons head tail =>
    (exists tail', (inserts x tail tail') /\ (List.cons head tail' = s))
  end.

Fixpoint permutes {X : Type} (l s : list X) : Prop :=
  match l with
  | List.nil => (s = List.nil)
  | List.cons head tail => exists tail',
                             (permutes tail tail') /\ (inserts head tail' s)
  end.

Theorem test_permutes : permutes (List.cons 1 (List.cons 2 (List.cons 3 List.nil)))
                                 (List.cons 3 (List.cons 2 (List.cons 1 List.nil))).
Proof.
  simpl. exists (List.cons 3 (List.cons 2 List.nil)).
  split.
  - exists (List.cons 3 List.nil). admit.
  - simpl. right. admit.
Admitted.
