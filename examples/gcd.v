(*
Copyright 2021 IMDEA Software Institute
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*)

From Stdlib Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype div.
From pcm Require Import axioms pred ordtype pcm heap.
From htt Require Import options model heapauto.

(* classical mutable Euclid's algorithm for computing GCD with subtractions *)

(* two memory cells holding intermediate values *)
Definition shape (p q : ptr) (x y : nat) :=
  [Pred h | exists h', h = p :-> x \+ (q :-> y \+ h')].

(* GCD loop invariant: at the end both cells contain the answer *)
(* (`unit` is needed because `Fix` always requires a single parameter) *)
Definition gcd_loopT (p q : ptr) : Type :=
  unit ->
  STsep {x y : nat} (shape p q x y,
                    [vfun (_ : unit) h =>
                       h \In shape p q (gcdn x y) (gcdn x y)]).

Program Definition gcd_loop (p q : ptr) :=
  ffix (fun (go : gcd_loopT p q) _ =>
    Do (x <-- !p;
        y <-- !q;
        if (x : nat) != y then
          if x < y then q ::= y - x;;
                        go tt
                   else p ::= x - y;;
                        go tt
        else skip)).
Next Obligation.
(* pull out ghosts + precondition (the shape of the heap) *)
move=>p q go _ [x [y _]] /= _ [h' ->].
(* read the numbers, do a 3-way comparison, run one more step in each branch *)
do 2!step; case: ltngtP=>/= [H|H|->]; step; last first.
- (* x=y, the program is finished because GCD(y,y) = y *)
  by move=>_; rewrite gcdnn; vauto.
- (* y<x, do the recursive call, deconstruct the shape *)
  apply: [gE (x-y), y]=>//=; first by eauto.
  move=>{h'} _ _ [m ->] _; exists m.
  (* use the difference property of GCD *)
  suff {p q go m}: gcdn (x - y) y = gcdn x y by move=>->.
  (* mathcomp's GCD theory uses addition, so we do a bit of arithmetical reasoning *)
  by rewrite gcdnC -gcdnDr gcdnC subnK //; apply: ltnW.
(* x<y, symmetrical case to above *)
apply: [gE x, (y-x)]=>//=; first by eauto.
move=>{h'}_ _ [m ->] _; exists m.
suff {p q go m}: gcdn x (y - x) = gcdn x y by move=>->.
by rewrite -gcdnDr subnK //; apply: ltnW.
Qed.

(* There's no guarantee on termination, as this is partial correctness. *)
(* The algorithm loops if u = 0 /\ v != 0 or vice versa *)
Program Definition gcd u v :
  STsep (PredT, [vfun r _ => r = gcdn u v]) :=
  (* allocate in the reverse order because the symbolic heap behaves as a stack *)
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
(* initialize the two cells, run the loop, deconstruct the shape *)
step=>q; step=>p; apply: [stepE u, v]=>//=; first by eauto.
move=>_ _ [h' ->].
(* run the rest of the program *)
by do 4!step; rewrite !unitL.
Qed.
