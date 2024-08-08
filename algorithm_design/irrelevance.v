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

Theorem safe_head_aux' : 0 > 0 -> False.
Proof.
  intros. inversion H.
Qed.

Definition safe_head {X : Type} (l : list X) : forall (H: length l > 0), X :=
  lift
    match l return (unused (length l > 0) X) with
    | nil => (inl safe_head_aux')
    | cons h t => inr h
    end.

Theorem safe_head_equal : forall X (l : list X) H H',
  safe_head l H = safe_head l H'.
Proof.
  intros X l. unfold safe_head. apply unused_does_not_matter.
Qed.
