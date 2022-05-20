From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype div.
From fcsl Require Import axioms pred pcm heap.
From HTT Require Import model heapauto.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Obligation Tactic := auto.

Definition pair (p q : ptr) (a b : nat) :=
  [Pred h | exists h', h = p :-> a \+ (q :-> b \+ h')].

Definition gcd_loopT (x y : ptr) : Type :=
  unit ->
  {a b : nat}, STsep (pair x y a b,
                     [vfun (_ : unit) h =>
                        h \In pair x y (gcdn a b) (gcdn a b)]).

Program Definition gcd_loop (a b : ptr) : gcd_loopT a b :=
  Fix (fun (go : gcd_loopT a b) _ =>
       Do (x <-- !a;
           y <-- !b;
           if (x : nat) != y then
             if x < y then b ::= y - x;;
                           go tt
                      else a ::= x - y;;
                           go tt
           else ret tt)).
Next Obligation.
move=>a b  go _ [x [y _]] /= _ [h' ->].
do 2!step; case: eqP=>/=.
- move=>->; step=>_.
  by rewrite gcdnn; vauto.
move=>E; case: ltngtP=>// {E}H; step.
- apply: [gE x, (y-x)]=>/=; first by eauto.
  case=>//= _ _ _ [m ->]; exists m.
  suff: gcdn x (y - x) = gcdn x y by move=>->.
  by rewrite -gcdnDr subnK //; apply: ltnW.
apply: [gE (x-y), y]=>//=; first by eauto.
case=>//= _ _ _ [m ->]; exists m.
suff: gcdn (x - y) y = gcdn x y by move=>->.
by rewrite gcdnC -gcdnDr gcdnC subnK //; apply: ltnW.
Qed.

(* note that there's no guarantee on termination *)
(* i.e. the algorithm will get stuck if u = 0 /\ v != 0 or vice versa *)
Program Definition gcd u v :
  STsep (PredT, [vfun r h => r = gcdn u v]) :=
  Do (a <-- alloc u;
      b <-- alloc v;
      gcd_loop a b tt;;
      x <-- !a;
      dealloc a;;
      dealloc b;;
      ret x).
Next Obligation.
move=>u v _ m /= _.
step=>x; step=>y; apply: [stepE u, v]=>/=.
- by rewrite joinCA; eauto.
case=>//= _ _ [h' ->].
by do 4!step; rewrite !unitL.
Qed.
