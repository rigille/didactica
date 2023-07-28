From Coq Require Import List Permutation.

Check list.

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