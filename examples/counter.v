(*
Copyright 2010 IMDEA Software Institute
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

From mathcomp Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype.
From pcm Require Import options axioms prelude pred.
From pcm Require Import pcm unionmap heap.
From htt Require Import options model heapauto.

(* counter that hides local state with an abstract predicate *)

Prenex Implicits exist.

Record cnt : Type :=
  Counter {inv : nat -> Pred heap;
           method : STsep {v : nat} (inv v,
                                    [vfun y m => y = v /\ m \In inv v.+1])}.

Program Definition new : STsep (emp, [vfun y m => m \In inv y 0]) :=
  Do (x <-- alloc 0;
      ret (@Counter (fun v => [Pred h | h = x :-> v])
                    (Do (y <-- !x;
                         x ::= y.+1;;
                         ret y)))).
Next Obligation.
by move=>x [v][] _ /= ->; do 3!step.
Qed.
Next Obligation.
move=>[] _ /= ->.
(* ordinarily step should work here *)
(* but it doesn't; we suspect because universe levels are off *)
(* but error messages aren't helpful *)
(* one can still finish the step manually *)
apply/vrf_bnd/vrf_alloc=>x; rewrite unitR=>_.
(* after which, automation proceeds to work *)
by step.
Qed.

(* Hiding local state with an abstract predicate is logically expensive,  *)
(* as the resulting abstract package must have a large type (since it     *)
(* includes a heap predicate). Hence, the package cannot be stored into   *)
(* the heap.                                                              *)
(*                                                                        *)
(* This is not particularly hurtful in the current model, since the model *)
(* assigns large types to computations anyway. But the later can easily   *)
(* be changed using the Petersen-Birkedal denotational model.             *)
(*                                                                        *)
(* Once we switch to the new model, we can hide the local state of the    *)
(* object by abstracting over the "representation" of the inv predicate,  *)
(* as follows.                                                            *)

Inductive rep : Type := Rep of ptr & nat.
Definition rptr r := let: Rep l _ := r in l.
Definition rval r := let: Rep _ v := r in v.
Definition interp (r : rep) : Pred heap := [Pred h | h = rptr r :-> rval r].

Record scnt : Type :=
  SCount {sinv : nat -> rep;
          smethod : STsep {v : nat} 
                      (interp (sinv v),
                      [vfun y m => y = v /\ m \In interp (sinv v.+1)])}.

Program Definition snew : STsep (emp,
                                [vfun y m => m \In interp (sinv y 0)]) :=
  Do (x <-- alloc 0;
      ret (@SCount (fun v => Rep x v)
                    (Do (y <-- !x;
                        x ::= y.+1;;
                        ret y)))).
Next Obligation.
move=>x [v][] i; rewrite /interp /= => {i}->.
by do 3!step.
Qed.
Next Obligation.
move=>[] _ /= ->.
apply/vrf_bnd/vrf_alloc=>x; rewrite unitR=>_.
by step.
Qed.

(* This solution replaces the abstract predicate inv with a type of     *)
(* representations, and a semantic function that interprets the         *)
(* representation into a predicate. We will typically want to prevent   *)
(* clients from looking at the representation, which can be done either *)
(* by making the type rep abstract, or by using some kind of            *)
(* computational irrelevance to make the sinv component of scnd         *)
(* inaccessible to programs. One possible solution for the later is to  *)
(* add new irrelevance constructors into type theory, as                *)
(* suggested by Pfenning, or Barras.                                    *)
(*                                                                      *)
(* Or, one can choose inv to have the type nat -> rep -> Prop, as shown *)
(* below. The type nat -> rep -> Prop is still a small type (it doesn't *)
(* quantify over heaps). So a package containing such an invariant will *)
(* be storable in the heap.                                             *)

Definition pinterp (R : rep -> Prop) : Pred heap :=
  [Pred h | forall r, R r -> h = rptr r :-> rval r].

Record pcnt : Type :=
  PCount {pinv : nat -> rep -> Prop;
          pmethod : STsep {v : nat} 
                      (pinterp (pinv v),
                      [vfun y m => y = v /\ m \In pinterp (pinv v.+1)])}.

Program Definition pnew : STsep (emp,
                                [vfun y m => m \In pinterp (pinv y 0)]) :=
  Do (x <-- alloc 0;
      ret (@PCount (fun v r => r = Rep x v)
                    (Do (y <-- !x;
                        x ::= y.+1;;
                        ret y)))).
Next Obligation.
move=>x [v][] i /=; rewrite /pinterp /= => /(_ _ erefl) {i}-> /=.
by do 3!step; move=>?; split=>// _ ->.
Qed.
Next Obligation.
move=>[] _ /= ->.
apply/vrf_bnd/vrf_alloc=>x; rewrite unitR=>_.
by step=>_ /= _  ->.
Qed.

(* Of course, the solution is still not quite abstract, since one cannot   *)
(* store the interpretation function together with the package, but that   *)
(* seems unavoidable due to the restrictions of impredicativity.  We have  *)
(* still gained something by using representations, however; we have made  *)
(* programs with local state storable -- something that is not possible    *)
(* if we use abstraction over heap predicates.                             *)
(*                                                                         *)
(* An altogether different approach is to define heaps as storing not      *)
(* types, but type representations, with a global interpretation           *)
(* function. The later, being global, will not need to be stored into      *)
(* heaps. Then heaps will be a small type, and we can freely abstract over *)
(* them. This lifts the representation approach to a global level, making  *)
(* it potentially more uniform, but it also makes it seemingly much more   *)
(* difficult.                                                              *)
