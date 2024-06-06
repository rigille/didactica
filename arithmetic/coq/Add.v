Require Import BinInt List.
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

Fixpoint add_aux (base : Z) (carry : bool)
  (digits : list (Z * Z)) : list Z :=
  match digits with
  | [] => []
  | (cons
      (left_head, right_head)
      tail) =>
    let c := (if carry then 1%Z else 0%Z) in
    let temporary := (Z.modulo (c + left_head) base) in
    let result := (Z.modulo (temporary + right_head) base) in
    let next_carry := (orb
                        (Z.ltb temporary c)
                        (Z.ltb result right_head)) in
    (cons
      result
      (add_aux base next_carry tail))
  end.

Definition add (base : Z) (a b : list Z) : list Z :=
  (add_aux base false (combine_default 0 0 a b)).

Compute (add 10%Z [9; 9; 2] [1]).
