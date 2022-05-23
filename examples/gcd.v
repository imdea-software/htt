From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype div.
From fcsl Require Import axioms pred pcm heap.
From HTT Require Import model heapauto.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Obligation Tactic := auto.

Definition pair (p q : ptr) (x y : nat) :=
  [Pred h | exists h', h = p :-> x \+ (q :-> y \+ h')].

Definition gcd_loopT (p q : ptr) : Type :=
  unit ->
  {x y : nat}, STsep (pair p q x y,
                     [vfun (_ : unit) h =>
                        h \In pair p q (gcdn x y) (gcdn x y)]).

Program Definition gcd_loop (p q : ptr) : gcd_loopT p q :=
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
move=>p q go _ [x [y _]] /= _ [h' ->].
do 2!step; case: ltngtP=>/= [H|H|->]; step; last first.
- by move=>_; rewrite gcdnn; vauto.
- apply: [gE (x-y), y]=>//=; first by eauto.
  case=>//= _ _ _ [m ->]; exists m.
  suff: gcdn (x - y) y = gcdn x y by move=>->.
  by rewrite gcdnC -gcdnDr gcdnC subnK //; apply: ltnW.
apply: [gE x, (y-x)]=>/=; first by eauto.
case=>//= _ _ _ [m ->]; exists m.
suff: gcdn x (y - x) = gcdn x y by move=>->.
by rewrite -gcdnDr subnK //; apply: ltnW.
Qed.

(* note that there's no guarantee on termination *)
(* i.e. the algorithm will get stuck if u = 0 /\ v != 0 or vice versa *)
Program Definition gcd u v :
  STsep (PredT, [vfun r _ => r = gcdn u v]) :=
  Do (p <-- alloc u;
      q <-- alloc v;
      gcd_loop p q tt;;
      x <-- !p;
      dealloc p;;
      dealloc q;;
      ret x).
Next Obligation.
move=>u v _ m /= _.
step=>x; step=>y; apply: [stepE u, v]=>/=.
- by rewrite joinCA; eauto.
case=>//= _ _ [h' ->].
by do 4!step; rewrite !unitL.
Qed.
