Require Import BinInt List Lia ZArith.
Import ListNotations.
(* Require Import Didactica.Main. *)
Local Open Scope Z_scope.

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
  (x : X) (y : Y)
  (lx : list X) (ly : list Y) : list (X * Y) :=
  match lx with
  | [] => repeat_left x ly
  | (cons hlx tlx) =>
      match ly with
      | [] => (repeat_right (cons hlx tlx) y)
      | (cons hly tly) =>
          (hlx, hly) :: (combine_default x y tlx tly)
      end
  end.

Definition bool_to_Z := Z.b2z.

Definition full_adder (base : Z) (carry : bool)
  (left right : Z) : bool * Z :=
    let c := bool_to_Z carry in
    let temporary := (Z.modulo (c + left) base) in
    let result := (Z.modulo (temporary + right) base) in
    let next_carry := (orb
                        (Z.ltb temporary c)
                        (Z.ltb result right)) in
    (next_carry, result).

Lemma add_back_to_bool :
  forall base carry left right,
  let c := Z.b2z carry in
  let temporary := (Z.modulo (c + left) base) in
  let result := (Z.modulo (temporary + right) base) in
  (eq
    (Z.add
      (Z.b2z (temporary <? Z.b2z carry))
      (Z.b2z (result <? right)))
    (Z.b2z
      (orb
        (Z.ltb temporary (Z.b2z carry))
        (Z.ltb result right)))).
Proof.
Admitted.

Fixpoint add_aux (base : Z) (carry : bool)
  (digits : list (Z * Z)) : list Z :=
  match digits with
  | [] => []
  | (cons
      (left_head, right_head)
      tail) =>
    let (next_carry, result) :=
      full_adder base carry left_head right_head in
    (cons
      result
      (add_aux base next_carry tail))
  end.

Definition number_add (base : Z) (a b : list Z) : list Z :=
  (add_aux base false (combine_default 0 0 a b)).

(* Search (?a * ?b -> ?a). *)

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

(*
Theorem overflow_check : forall base a b,
  0 <= a < base ->
  0 <= b < base ->
  let remainder := (Z.modulo (a + b) base) in
  (eq
    remainder
    (if Z.ltb remainder a then
      (a + b - base)
    else
      (a + b))).
Proof.
  intros. subst remainder.
  rewrite (possible_remainders base a b H H0).
  destruct (Z.ltb (a + b) base) eqn:Bound. {
    replace (Z.ltb (a + b) a) with false by lia.
    reflexivity.
  } {
    replace (Z.ltb (a + b - base) a) with true by lia.
    reflexivity.
  }
Qed.
*)

Theorem possible_remainders : forall base a b,
  0 <= a < base ->
  0 <= b < base ->
  (eq
    (Z.modulo (a + b) base)
    (if Z.ltb (a + b) base then 
      (a + b)
    else
      (a + b - base))).
Proof.
  intros.
  assert (0 <= a + b < 2*base) by lia.
  destruct (Z.ltb (a + b) base) eqn:Bound.
  - apply Z.mod_small. lia.
  - assert (0 <= a + b - base < base) by lia.
    rewrite <- (Z.mod_add (a + b) (-1) base ltac:(lia)).
    replace (a + b + (-1 * base)) with
            (a + b - base) by lia.
    apply Z.mod_small. assumption.
Qed.

Theorem full_adder_spec :
  forall base carry n m,
  1 < base ->
  0 <= n < base ->
  0 <= m < base ->
  let (next_carry, result) := full_adder base carry n m in
  (eq
    (n + m + bool_to_Z carry)
    (base*(bool_to_Z next_carry) + result)).
Proof.
  intros base carry n m BaseBig NBound MBound.
  unfold full_adder.
  remember (bool_to_Z carry) as c eqn:CDefinition.
  assert (0 <= c <= 1) by (destruct carry; subst c; simpl; lia).
  remember (Z.modulo (c + n) base)
    as remainder eqn:RemainderDefinition.
  rewrite (possible_remainders base c n ltac:(lia) NBound)
    in RemainderDefinition.
  destruct (Z.ltb (Z.add c n) base) eqn:OverflowCheck0. {
    replace (Z.ltb remainder c) with false by lia.
    simpl.
    rewrite (possible_remainders base remainder m ltac:(lia) MBound).
    destruct (Z.ltb (Z.add remainder m) base). {
      replace (Z.ltb (Z.add remainder m) m) with false by lia.
      simpl. subst remainder. lia.
    } {
      replace (Z.ltb (remainder + m - base) m) with true by lia.
      simpl. subst remainder. lia.
    }
  } {
    replace (Z.ltb remainder c) with true by lia. simpl.
    rewrite (possible_remainders base remainder m ltac:(lia) MBound).
    destruct (Z.ltb (Z.add remainder m) base) eqn:OverflowCheck2. {
      subst remainder. lia.
    } {
      exfalso. lia.
    }
  }
Qed.

Theorem full_adder_adds :
  forall base carry r0 q0 r1 q1,
  1 < base ->
  0 <= r0 < base ->
  0 <= r1 < base ->
  let c := bool_to_Z carry in
  let (next_carry, result) := full_adder base carry r0 r1 in
  (eq
    ((base*q0 + r0) + (base*q1 + r1) + c)
    (base*(q0 + q1 + (bool_to_Z next_carry)) + result)).
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
      (r0 + r1 + bool_to_Z carry)
    with
      (base*(bool_to_Z next_carry) + result). {
      lia.
    } {
      rewrite full_adder_spec with (base:=base); try assumption.
      unfold full_adder in FullAdderInvocation.
      inversion FullAdderInvocation; reflexivity.
    }
  }
Qed.
