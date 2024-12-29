Require Import BinInt List Lia ZArith.
Import ListNotations.
(* Require Import Didactica.Main. *)
Local Open Scope Z_scope.

Definition reduce_let {X Y Z} (p : X * Y) (c : X -> Y -> Z) :
  (let (a, b) := p in (c a b)) = (c (fst p) (snd p)).
Proof.
  destruct p.
  reflexivity.
Qed.

Fixpoint repeat_left {X Y : Type}
  (x : X) (ly : list Y) : list (X * Y) :=
  match ly with
  | [] => []
  | (cons hly tly) => (cons (x, hly) (repeat_left x tly))
  end.

Fixpoint repeat_right {X Y : Type}
  (lx : list X) (y : Y) : list (X * Y) :=
  match lx with
  | [] => []
  | (cons hlx tlx) => (cons (hlx, y) (repeat_right tlx y))
  end.

Fixpoint combine_default {X Y : Type}
  (x : X) (y : Y) (size : nat)
  (lx : list X) (ly : list Y) : list (X * Y) :=
  match size with
  | O => []
  | S pred =>
      (cons
        ((hd x lx), (hd y ly))
        (combine_default x y pred (tl lx) (tl ly)))
  end.

Fixpoint fold_map {X Y Z}
  (f : Y -> X -> Y * Z) (y : Y) (l : list X) : Y * (list Z) :=
  match l with
  | [] => (y, [])
  | h :: t =>
    let (next_y, next_x) := f y h in
    let (final_y, final_tail) := (fold_map f next_y t) in
    (final_y, next_x :: final_tail)
  end.

Theorem fold_map_concatenate : forall {X Y Z} a b (f : Y -> X -> Y * Z) y,
  (eq
    (fold_map f y (a ++ b))
    (let (intermediate_y, new_a) := fold_map f y a in
    let (final_y, new_b) := fold_map f intermediate_y b in
    (final_y, new_a ++ new_b))).
Proof.
  induction a; intros.
  - simpl. destruct (fold_map f y b); reflexivity.
  - simpl. remember (f y a) as current_iteration.
    rewrite reduce_let with (p := current_iteration).
    rewrite reduce_let with (p := current_iteration).
    rewrite IHa.
    remember
      (fold_map f (fst current_iteration) a0)
    as first_leg.
    rewrite reduce_let with (p := first_leg).
    rewrite reduce_let with (p := first_leg).
    remember
      (fold_map f (fst first_leg) b)
    as second_leg.
    rewrite reduce_let with (p := second_leg).
    rewrite reduce_let with (p := second_leg).
    reflexivity.
Qed.

Theorem fold_map_length : forall {X Y Z} l (f : Y -> X -> Y * Z) y,
  (eq
    (length l)
    (length (snd (fold_map f y l)))).
Proof.
  induction l; intros.
  - reflexivity.
  - simpl. rewrite reduce_let. rewrite reduce_let.
    simpl. rewrite <- IHl with (f := f) (y := (fst (f y a))). 
    reflexivity.
Qed.

Definition theoretical_full_adder (base : Z) (carry : bool)
  (left right : Z) : bool * Z :=
  let carry_z := Z.b2z carry in
  let sum := carry_z + left + right in
  let carry_out := (negb (Z.ltb sum base)) in
  (carry_out, sum mod base).

Definition full_adder (base : Z) (carry : bool)
  (left right : Z) : bool * Z :=
    let c := Z.b2z carry in
    let temporary := (Z.modulo (c + left) base) in
    let result := (Z.modulo (temporary + right) base) in
    let next_carry := (orb
                        (Z.ltb temporary c)
                        (Z.ltb result right)) in
    (next_carry, result).

Lemma bool_bound : forall b,
  0 <= (Z.b2z b) <= 1.
Proof.
  intros; destruct b; simpl; lia.
Qed.

Lemma bool_digit_bound : forall base b,
  1 < base ->
  0 <= (Z.b2z b) < base.
Proof.
  intros. generalize (bool_bound b); lia.
Qed.

Theorem full_adder_result_small :
  forall base carry left right,
  1 < base ->
  0 <= left < base ->
  0 <= right < base ->
  0 <= snd (full_adder base carry left right) < base.
Proof.
  intros. simpl. apply Z.mod_pos_bound.
  lia.
Qed.

Theorem digit_addition_bound : forall base carry left right,
  0 <= left < base ->
  0 <= right < base ->
  let carry_z := Z.b2z carry in
  0 <= carry_z + left + right < 2*base.
Proof.
  intros base carry left right left_bound right_bound carry_z.
  generalize (bool_bound carry); lia.
Qed.

Theorem possible_remainders : forall base carry a b,
  0 <= a < base ->
  0 <= b < base ->
  let carry_z := Z.b2z carry in
  (eq
    (Z.modulo (carry_z + a + b) base)
    (if Z.ltb (carry_z + a + b) base then 
      (carry_z + a + b)
    else
      (carry_z + a + b - base))).
Proof.
  intros base carry a b a_bound b_bound carry_z.
  generalize
    (digit_addition_bound
      base carry a b a_bound b_bound); intros add_bound.
  generalize (bool_bound carry); intros carry_bound.
  destruct (Z.ltb (carry_z + a + b) base) eqn:bound.
  - apply Z.mod_small. lia.
  - assert (0 <= carry_z + a + b - base < base) by lia.
    rewrite <- (Z.mod_add (carry_z + a + b) (-1) base ltac:(lia)).
    replace (carry_z + a + b + (-1 * base)) with
        (carry_z + a + b - base) by lia.
    apply Z.mod_small. assumption.
Qed.

Theorem overflow_check : forall base a b,
  0 <= a < base ->
  0 <= b < base ->
  let remainder := (Z.modulo (a + b) base) in
  (eq
    (remainder <? a)
    (negb (a + b <? base))).
Proof.
  intros base a b a_bound b_bound.
  replace (a + b) with (Z.b2z false + a + b) by reflexivity.
  rewrite possible_remainders; try assumption.
  simpl.
  destruct
    (a + b <? base)
  eqn:condition_definition; lia.
Qed.

Theorem impossible_overflows : forall base carry left right,
  1 < base ->
  0 <= left < base ->
  0 <= right < base ->
  let carry_z := Z.b2z carry in
  let temporary := (Z.modulo (carry_z + left) base) in
  let result := (Z.modulo (temporary + right) base) in
  (not (and
    (Z.lt temporary carry_z)
    (Z.lt result right))).
Proof.
  intros base carry left right base_big left_bound right_bound.
  simpl.
  rewrite <- Z.ltb_lt.
  rewrite <- Z.ltb_lt.
  generalize (bool_bound carry); intros carry_bound.
  generalize
    (Z.mod_pos_bound (Z.b2z carry + left) base ltac:(lia));
  intros.
  rewrite overflow_check; try assumption; try lia.
  replace 
    ((Z.b2z carry + left) mod base + right)
  with
    (right + (Z.b2z carry + left) mod base)
  by lia.
  rewrite overflow_check; try assumption.
  destruct
    (Z.b2z carry + left <? base)
  eqn:overflow0. lia.
  replace (Z.b2z carry + left) with base by lia.
  rewrite Z_mod_same_full.
  lia.
Qed.

Theorem full_adders_agree :
  forall base carry n m,
  1 < base ->
  0 <= n < base ->
  0 <= m < base ->
  (eq
    (full_adder base carry n m)
    (theoretical_full_adder base carry n m)).
Proof.
  intros base carry n m base_big n_bound m_bound.
  unfold full_adder, theoretical_full_adder.
  apply pair_equal_spec; split. {
    rewrite
      (overflow_check
        base (Z.b2z carry) n
        (bool_digit_bound base carry base_big) n_bound).
    destruct (Z.b2z carry + n <? base) eqn:overflow_0. {
      rewrite
        (Z.add_comm ((Z.b2z carry + n) mod base) m).
      generalize
        (Z.mod_pos_bound 
          (Z.b2z carry + n) base ltac:(lia)); intros.
      rewrite
        (overflow_check
          base m ((Z.b2z carry + n) mod base)
          m_bound ltac:(lia)).
      rewrite <-
      (Z.add_comm ((Z.b2z carry + n) mod base) m).
      replace ((Z.b2z carry + n) mod base)
      with (Z.b2z carry + n). reflexivity.
      rewrite Z.mod_small. reflexivity.
      generalize (bool_bound carry); intros.
      lia.
    } {
      replace
        ((Z.b2z carry + n) mod base + m)
      with
        (m + (Z.b2z carry + n) mod base)
      by lia.
      rewrite
        (overflow_check
          base m ((Z.b2z carry + n) mod base)); try lia.
      apply Z.mod_pos_bound. lia.
    }
  } {
    remember (Z.b2z carry) as carry_z eqn:carry_z_definition.
    apply (Zplus_mod_idemp_l (carry_z + n) m base).
  } 
Qed.


(**
  Let's say we have any (base : Z) (carry : bool) (left right : Z)
  such that
    base_big : 1 < base
    left_bound : 0 <= left < base
    right_bound : 0 <= right < base
  and define (carry_z := Z.bool_to_Z carry) the usual
  representation of bools as 0 or 1.
  now let's consider (carry_z + left + right) mod base. We need to
  calculate this without using any number that exceeds base in value
  throughout the calculation, since this is what we have available in
  the cpu. First of all since we're talking about integers, we can
  deduce the tighter bounds
    left_bound' : 0 <= left <= base - 1
    right_bound' : 0 <= right <= base - 1
  adding them together
    partial_bound : 0 <= left + right <= 2*base - 2
  now since we have (bool_bound carry) : 0 <= carry_z <= 1, we can
  add that and obtain
    full_bound' : 0 <= carry_z + left + right <= 2*base - 1
    full_bound : 0 <= carry_z + left + right < 2*base
  now what's ((carry_z + left + right) mod base)? It depends on the
  value of first_condition : (Z.ltb (carry_z + left + right) base).
  If it's true then
    ((carry_z + left + right) mod base) = carry_z + left + right
  If it's false then we have
    base <= carry_z + left + right
  but remembering full_bound
    base <= carry_z + left + right < 2*base
    0 <= carry_z + left + right - base < base
  therefore
    (eq
      ((carry_z + left + right) mod base)
      (carry_z + left + right - base))
*)

Lemma add_back_to_bool :
  forall base carry left right,
  1 < base ->
  0 <= left < base ->
  0 <= right < base ->
  let carry_z := Z.b2z carry in
  let temporary := (Z.modulo (carry_z + left) base) in
  let result := (Z.modulo (temporary + right) base) in
  (eq
    (Z.add
      (Z.b2z (temporary <? carry_z))
      (Z.b2z (result <? right)))
    (Z.b2z
      (orb
        (Z.ltb temporary carry_z)
        (Z.ltb result right)))).
Proof.
  intros base carry left right base_big left_bound right_bound
  carry_z temporary result.
  destruct (temporary <? carry_z) eqn:overflow0;
  destruct (result <? right) eqn: overflow1;
  try reflexivity.
  generalize
    (impossible_overflows
      base carry left right base_big left_bound right_bound);
  intros contra.
  exfalso. simpl in contra; subst carry_z temporary result;
  lia.
Qed.

Definition add_aux_body (base : Z) (record : (list Z) * bool) (current : Z * Z) :=
  let (left, right) := current in
  let (partial, carry_in) := record in
  let (carry_out, sum) := full_adder base carry_in left right in
  (partial ++ [sum], carry_out).

(* TODO: use fold_map *)
Definition add_aux' (base : Z) (carry : bool)
  (digits : list (Z * Z)) : (list Z) * bool :=
  fold_left
    (add_aux_body base)
    digits
    ([], carry).

Fixpoint add_aux (base : Z) (carry : bool)
  (digits : list (Z * Z)) : list Z * bool :=
  match digits with
  | [] => ([], carry)
  | (cons
      (left_head, right_head)
      tail) =>
    let (next_carry, result) :=
      full_adder base carry left_head right_head in
    let (added_tail, final_carry) := add_aux base next_carry tail in
    ((cons
      result
      added_tail), final_carry)
  end.

Definition number_add_body (base : Z) (carry : bool) (digits : Z * Z) : bool * Z :=
  let (left_head, right_head) := digits in
  full_adder base carry left_head right_head.

Definition number_add (base : Z) (carry : bool) (a b : list Z) (size : nat) : bool * list Z :=
  fold_map (number_add_body base) carry (combine_default 0 0 size a b).

Theorem length_cons : forall {X} (h : X) (t : list X),
  length (h :: t) = S (length t).
Proof.
  reflexivity.
Qed.

Theorem combine_default_length : forall {X Y} size a b (x : X) (y : Y),
  length (combine_default x y size a b) = size.
Proof.
  induction size; intros.
  - reflexivity.
  - simpl. rewrite IHsize. reflexivity.
Qed.

Theorem number_add_length :
  forall (size : nat) (base : Z) (carry : bool) (a b : list Z),
  length (snd (number_add base carry a b size)) = size.
Proof.
  intros.
  unfold number_add.
  remember
    (fun (y : bool) (x : Z * Z) =>
      let (left_head, right_head) := x in
      full_adder base y left_head right_head)
  as f.
  rewrite <- combine_default_length with
  (a := a) (b := b) (x := 0) (y := 0).
  symmetry. apply fold_map_length.
Qed.

Theorem full_adder_spec :
  forall base carry n m,
  1 < base ->
  0 <= n < base ->
  0 <= m < base ->
  let (next_carry, result) := full_adder base carry n m in
  (eq
    (n + m + Z.b2z carry)
    (base*(Z.b2z next_carry) + result)).
Proof.
  intros base carry n m base_big n_bound m_bound.
  rewrite
    (full_adders_agree base carry n m base_big n_bound m_bound).
  unfold theoretical_full_adder.
  rewrite (possible_remainders base carry n m n_bound m_bound).
  remember (Z.b2z carry) as carry_z eqn:carry_z_definition.
  destruct (carry_z + n + m <? base); simpl; lia.
Qed.

Theorem full_adder_adds :
  forall base carry r0 q0 r1 q1,
  1 < base ->
  0 <= r0 < base ->
  0 <= r1 < base ->
  let c := Z.b2z carry in
  let (next_carry, result) := full_adder base carry r0 r1 in
  (eq
    ((base*q0 + r0) + (base*q1 + r1) + c)
    (base*(q0 + q1 + (Z.b2z next_carry)) + result)).
Proof.
  intros base carry r0 q0 r1 q1 BaseBig R0Bound
    R1Bound c.
  destruct (full_adder base carry r0 r1) as [next_carry result]
    eqn:FullAdderInvocation.
  transitivity (base*(q0 + q1) + (r0 + r1 + c)). {
    lia.
  } {
    subst c.
    replace 
      (r0 + r1 + Z.b2z carry)
    with
      (base*(Z.b2z next_carry) + result). {
      lia.
    } {
      rewrite full_adder_spec with (base:=base); try assumption.
      unfold full_adder in FullAdderInvocation;
      inversion FullAdderInvocation; reflexivity.
    }
  }
Qed.

Theorem full_adder_bounded :
  forall base carry left right,
  1 < base ->
  -1 < left < base ->
  -1 < right < base ->
  -1 < (snd (full_adder base carry left right)) < base.
Proof.
Admitted.

Definition base_bound (base : Z) (digit : Z) :=
  -1 < digit < base.

Definition double_base_bound (base : Z) (pair : Z * Z) :=
  (and
    (-1 < (fst pair) < base)
    (-1 < (snd pair) < base)).

Definition number_bound (base : Z) (digits : list Z) :=
  Forall (base_bound base) digits.

Theorem combine_default_bounded : forall base size a b,
  1 < base ->
  number_bound base a ->
  number_bound base b ->
  Forall (double_base_bound base) (combine_default 0 0 size a b).
Proof.
  induction size; intros.
  - simpl. apply Forall_nil.
  - simpl. apply Forall_cons.
    * unfold double_base_bound.
      simpl. split.
      + destruct a. simpl. lia.
        simpl. inversion H0; subst. apply H4.
      + destruct b. simpl. lia.
        simpl. inversion H1; subst.  apply H4.
    * apply IHsize. apply H.
      + destruct a. apply Forall_nil. inversion H0; subst.
        apply H5.
      + destruct b. apply Forall_nil. inversion H1; subst.
        apply H5.
Qed.

Theorem number_add_bound :
  forall (base : Z) (carry : bool) (a b : list Z) (size : nat),
  1 < base ->
  number_bound base a ->
  number_bound base b ->
  Forall (base_bound base) (snd (number_add base carry a b size)).
Proof.
  unfold number_add. intros.
  generalize
    (combine_default_bounded base size a b H H0 H1).
  revert carry.
  generalize dependent (combine_default 0 0 size a b).
  induction l; intros.
  - simpl. apply Forall_nil.
  - inversion H2; subst. destruct a0 as [left_digit right_digit].
    unfold double_base_bound in H5. simpl in H5.
    inversion H5. clear H5.
    unfold add_aux; fold add_aux.
    unfold snd at 1. rewrite reduce_let. unfold fold_map; fold (@fold_map (Z * Z) bool).
    rewrite reduce_let.
    rewrite reduce_let. unfold snd at 1.
    apply Forall_cons.
    * unfold base_bound. apply full_adder_bounded; try assumption.
    * apply IHl. apply H6.
Qed.


Lemma nth_next : forall X (n : nat)
  (default : X) digits,
  (eq
    (nth
      (S n)
      digits
      default)
    (nth n (tl digits) default)).
Proof.
  intros.  destruct digits; simpl.
  - destruct n; reflexivity.
  - reflexivity. 
Qed.

Lemma nth_0 : forall X
  (default : X) digits,
  (eq
    (nth
      0
      digits
      default)
    (hd default digits)).
Proof.
  intros. destruct digits; reflexivity.
Qed.

Lemma tl_combine_default : forall X Y (n : nat)
  (left_default : X) (right_default : Y)
  left_digits right_digits,
  (eq
    (tl (combine_default
      left_default
      right_default
      (S n)
      left_digits
      right_digits))
    (combine_default
      left_default
      right_default
      n
      (tl left_digits)
      (tl right_digits))).
Proof.
Admitted.


Lemma combine_default_Sn : forall X Y (n : nat)
  (left_default : X) (right_default : Y)
  left_digits right_digits,
  (eq
    (combine_default
      left_default
      right_default
      (S n)
      left_digits
      right_digits)
    (app
      (combine_default
        left_default
        right_default
        n
        left_digits
        right_digits)
      [(pair
        (nth n left_digits left_default)
        (nth n right_digits right_default))])).
Proof.
Admitted.

Lemma nth_combine : forall X Y (n m : nat)
  (H : (Nat.lt n m))
  (left_default : X) (right_default : Y)
  left_digits right_digits,
  (eq
    (nth
      n
      (combine_default left_default right_default m left_digits right_digits)
      (left_default, right_default))
    ((nth n left_digits left_default), (nth n right_digits right_default))).
Proof.
  induction n.
  - destruct m; intros.
    + inversion H.
    + simpl. rewrite nth_0. rewrite nth_0. reflexivity.
  - destruct m; intros.
    + inversion H.
    + simpl. rewrite nth_next. rewrite nth_next.
      apply IHn. lia.
Qed.

Search nth.

(*
Theorem fold_map_concatenate : forall {X Y Z} a b (f : Y -> X -> Y * Z) y,
  (eq
    (fold_map f y (a ++ b))
    (let (intermediate_y, new_a) := fold_map f y a in
    let (final_y, new_b) := fold_map f intermediate_y b in
    (final_y, new_a ++ new_b))).

Definition number_add (base : Z) (carry : bool) (a b : list Z) (size : nat) : bool * list Z :=
  fold_map (number_add_body base) carry (combine_default 0 0 size a b).
 *)

Theorem next_carry : forall n base carry left_number right_number,
(eq
  (fst
    (full_adder
      base
      (fst
         (number_add base carry left_number right_number n))
      (nth n left_number 0)
      (nth n right_number 0)))
  (fst
    (number_add
      base
      carry
      left_number
      right_number
      (S n)))).
Proof.
  Search (_ < _).
  intros.
  unfold number_add.
  rewrite combine_default_Sn.
  rewrite fold_map_concatenate.
  rewrite reduce_let.
  rewrite reduce_let.
  cbn [fst fold_map].
  rewrite reduce_let.
  cbn [fst number_add_body].
  reflexivity.
Qed.
(*
Forall digit_bound
  (fst
     (add_digits carry (number_digits left) (number_digits right)
        (Z.to_nat (pre_number_length output))))
*)
