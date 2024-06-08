Require Import BinInt List Lia.
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

Definition add (base : Z) (a b : list Z) : list Z :=
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

Theorem possible_remainders : forall base a b,
  0 <= a < base ->
  0 <= b < base ->
  let remainder := (Z.modulo (a + b) base) in
  (remainder = a + b) \/ (remainder = a + b - base).
Proof.
  intros.
  assert (0 <= a + b < 2*base) by lia.
  destruct (Z.lt_ge_cases (a + b) base).
  - left. (* Search (?a mod _ = ?a). *)
    apply Z.mod_small. lia.
  - right.
    assert (0 <= a + b - base < base) by lia.
    subst remainder.
    rewrite <- (Z.mod_add (a + b) (-1) base ltac:(lia)).
    replace (a + b + (-1 * base)) with
            (a + b - base) by lia.
    apply Z.mod_small. assumption.
Qed.

Theorem overflow_check : forall base a b,
  0 <= a < base ->
  0 <= b < base ->
  let remainder := (Z.modulo (a + b) base) in
  if Z.ltb remainder a then
    remainder = a + b - base
  else
    remainder = a + b.
Proof.
  intros.
  destruct (possible_remainders base a b H H0). {
    subst remainder. rewrite H1.
    replace (a + b <? a) with false by lia.
    reflexivity.
  } {
    subst remainder. rewrite H1.
    replace (a + b - base <? a) with true by lia.
    reflexivity.
  }
Qed.

Theorem full_adder_adds :
  forall base carry r0 q0 r1 q1,
  1 < base ->
  0 <= r0 < base ->
  0 <= r1 < base ->
  let c := bool_to_Z carry in
  let (next_carry, result) := full_adder base carry r0 r1 in
  (eq ((base*q0 + r0) + (base*q1 + r1) + c)
      (base*(q0 + q1 + (bool_to_Z next_carry)) + result)).
Proof.
  intros.
  transitivity (base*(q0 + q1) + r0 + r1 + c). lia.
  replace (bool_to_Z carry) with c by reflexivity.
  remember ((c + r0) mod base) as temporary.
  remember ((temporary + r1) mod base) as result.
  assert (0 <= c <= 1) by (subst c; destruct carry; simpl; lia).
  (* Search ((Z.lt ?a ?b) \/ _). *)
  destruct (Z.lt_ge_cases temporary c);
  destruct (Z.lt_ge_cases result r1).
  - (* two overflows are impossible *)
    replace (Z.ltb temporary c) with true by lia.
    replace (Z.ltb result r1) with true by lia.
    simpl.
    admit.
  - admit.
  - admit.
  - (* no overflows *)
    replace (temporary <? c) with false by lia.
    replace (result <? r1) with false by lia.
    simpl.
    assert (c + r0 < base). {
      admit.
    }
Admitted.

Compute (add 10%Z [9; 9; 2] [1]).
