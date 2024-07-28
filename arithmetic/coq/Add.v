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

Definition theoretical_full_adder (base : Z) (carry : bool)
  (left right : Z) : bool * Z :=
  let carry_z := Z.b2z carry in
  let sum := carry_z + left + right in
  let carry_out := Z.ltb base sum in
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

Search ((_ + _) mod _).

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

Lemma single_overflow : forall
  (base : Z) (carry : bool) (left right : Z),
  1 < base ->
  0 <= left < base ->
  0 <= right < base ->
  let c := Z.b2z carry in
  let temporary := (Z.modulo (c + left) base) in
  let result := (Z.modulo (temporary + right) base) in
  (or
    (and
      (temporary <? c = true)
      (result <? right = false))
    (and
      (temporary <? c = false)
      (result <? right = true))).
Proof.
  simpl. intros
  base carry left right base_bound left_bound right_bound.
  generalize
    (bool_bound carry); intros c_bound.
  remember (Z.b2z carry) as c eqn:c_definition.
  generalize
    (possible_remainders
      base c left ltac:(lia) left_bound);
  intros temporary_definition.
  remember ((c + left) mod base) as temporary.
  clear Heqtemporary.
  intros. (*
  destruct (Z.ltb temporary base) eqn:OverflowCheck0;
  destruct (Z.ltb result right).
  { {
    right. split. } {} }
  {}
           *)
Admitted.


Lemma add_back_to_bool :
  forall base carry left right,
  let c := Z.b2z carry in
  let temporary := (Z.modulo (c + left) base) in
  let result := (Z.modulo (temporary + right) base) in
  (eq
    (Z.add
      (Z.b2z (temporary <? c))
      (Z.b2z (result <? right)))
    (Z.b2z
      (orb
        (Z.ltb temporary c)
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
  intros base carry n m BaseBig NBound MBound.
  unfold full_adder.
  remember (Z.b2z carry) as c eqn:CDefinition.
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
      unfold full_adder in FullAdderInvocation.
      inversion FullAdderInvocation; reflexivity.
    }
  }
Qed.
