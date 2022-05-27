From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype div.
From fcsl Require Import axioms pred pcm heap.
From HTT Require Import model heapauto.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Obligation Tactic := auto.

(* classical mutable Euclid's algorithm for computing GCD with subtractions *)

(* two memory cells holding intermediate numbers *)
Definition pair (p q : ptr) (x y : nat) :=
  [Pred h | exists h', h = p :-> x \+ (q :-> y \+ h')].

(* GCD loop invariant *)
Definition gcd_loopT (p q : ptr) : Type :=
  unit ->
  {x y : nat}, STsep (pair p q x y,
                     [vfun (_ : unit) h =>
                        h \In pair p q (gcdn x y) (gcdn x y)]).

Program Definition gcd_loop (p q : ptr) :=
  Fix (fun (go : gcd_loopT p q) _ =>
       Do (x <-- !p;
           y <-- !q;
           if (x : nat) != y then
             if x < y then q ::= y - x;;
                           go tt
                      else p ::= x - y;;
                           go tt
           else ret tt)).
Next Obligation.
(* pull out ghosts + precondition (the shape of the heap) *)
move=>p q go _ [x [y _]] /= _ [h' ->].
(* read the numbers, do a 3-way comparison, run one more step in each branch *)
do 2!step; case: ltngtP=>/= [H|H|->]; step; last first.
- (* x=y, the program is finished because GCD(y,y) = y *)
  by move=>_; rewrite gcdnn; vauto.
- (* y<x, do the recursive call *)
  apply: [gE (x-y), y]=>//=; first by eauto.
  (* the result is always succesful (no exception are ever thrown) *)
  case=>//= _ _ _ [m ->]; exists m.
  (* use the difference property of GCD *)
  suff: gcdn (x - y) y = gcdn x y by move=>->.
  (* mathcomp's GCD theory uses addition, so we do a bit of arithmetical reasoning *)
  by rewrite gcdnC -gcdnDr gcdnC subnK //; apply: ltnW.
(* x<y, symmetrical case to above *)
apply: [gE x, (y-x)]=>/=; first by eauto.
case=>//= _ _ _ [m ->]; exists m.
suff: gcdn x (y - x) = gcdn x y by move=>->.
by rewrite -gcdnDr subnK //; apply: ltnW.
Qed.

(* note that there's no guarantee on termination *)
(* i.e. the algorithm will get stuck if u = 0 /\ v != 0 or vice versa *)
Program Definition gcd u v :
  STsep (PredT, [vfun r _ => r = gcdn u v]) :=
  (* we allocate in the reverse order because the symbolic heap behaves as a stack *)
  (* this way it'll match the specification perfectly, removing a bit of bureaucracy *)
  Do (q <-- alloc v;
      p <-- alloc u;
      gcd_loop p q tt;;
      x <-- !p;
      dealloc p;;
      dealloc q;;
      ret x).
Next Obligation.
(* simplify *)
move=>u v _ m /= _.
(* initialize the two cells, run the loop *)
step=>q; step=>p; apply: [stepE u, v]=>/=; first by eauto.
(* the result is never an exception *)
case=>//= _ _ [h' ->].
(* run the rest of the program *)
by do 4!step; rewrite !unitL.
Qed.
