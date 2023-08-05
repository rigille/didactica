From Coq Require Import List Permutation Nat Datatypes PeanoNat.
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

Fixpoint equivalent_insert (s : list nat) (n : nat) :=
  match s with
  | [] => n
  | sh :: st => let previous := equivalent_insert st n in
                let increment := if leb sh previous then 1 else 0 in
                increment + previous
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

* caso skipn sh = []

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


permute (i :: s0) (permute ((S pred) :: s1) (h :: t))
permute (i :: s0) (insert (S pred) h (permute s1 t))


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
