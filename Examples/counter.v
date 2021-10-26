From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.
From fcsl Require Import axioms pred.
From fcsl Require Import pcm unionmap heap.
From HTT Require Import domain stmod stsep stlog stlogR.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Obligation Tactic := auto.

(* counter that hides local state with an abstract predicate *)

Prenex Implicits exist.

Record cnt : Type :=
  Counter {inv : nat -> Pred heap;
           method : {v : nat}, STsep (inv v,
                                [vfun (y : nat) h => y = v /\ inv (v.+1) h])}.

(*
Lemma gw A x (v : A) : valid (x :-> v) -> (x :-> v) \In (pts x v).
Proof. by move=>A x v H; rewrite opn. Qed.

Hint Resolve gw.
*)
Program Definition new : STsep (emp, [vfun v => inv v 0]) :=
  Do (x <-- alloc 0;
      ret (@Counter (fun v h => h = x :-> v)
                    (Do (y <-- !x;
                        x ::= y.+1;;
                        ret y)))).
Next Obligation.
move=>x ? /= [y]->.
do 3!step; move=>V1 z H; rewrite validPt in V1.
suff: (y = z) by move=>->.
apply: (@hcancelPtV _ x)=>//.
by rewrite validPt.
Qed.
Next Obligation.
move=>? /= ->. apply: bnd_seq. apply: val_alloc.

apply (@bnd_allocR _ cnt (fun x => ret {|
                                           inv := fun v : nat => eq^~ (x :-> v);
                                           method := Do y <-- ! x; x ::= y.+1;; ret y
                                         |}) 0 Unit).
case: H=><-; apply: bnd_alloc=>// x; heval=>D; hhauto; rewrite unh0 /= in D *; auto.
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

Inductive rep : Type := Rep of loc & nat.
Definition ptr r := let: Rep l _ := r in l.
Definition val r := let: Rep _ v := r in v.
Definition interp (r : rep) : Rel heap := [Rel h | h \In ptr r --> val r].

Record scnt : Type :=
  SCount {sinv : nat -> rep;
          smethod : STsep nat (fun i => exists v, i \In interp (sinv v),
                               fun y i m => forall v, i \In interp (sinv v) ->
                                 y = Val v /\ m \In interp (sinv v.+1))}.

Program
Definition snew : STsep scnt (emp, fun y i m =>
                                     exists v, y = Val v /\ m \In interp (sinv v 0)) :=
  Do (x <-- alloc 0;
      ret (@SCount (fun v => Rep x v)
                    (Do (y <-- !x;
                        x ::= y.+1;;
                        ret y)))).
Next Obligation.
by case/swp: H0=>->; heval=>D1 w; case/opn=>D; heap_cancel=>//= _ _ ->; rewrite InE /= opn.
Qed.
Next Obligation.
by case: H=><-; apply: bnd_alloc=>// x; heval=>D; hhauto; rewrite unh0 InE /= opn in D *.
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

Definition pinterp (R : rep -> Prop) : Rel heap :=
  [Rel h | forall r, R r -> h \In ptr r --> val r].

Record pcnt : Type :=
  PCount {pinv : nat -> rep -> Prop;
          pmethod : STsep nat (fun i => exists v, i \In pinterp (pinv v),
                               fun y i m => forall v, i \In pinterp (pinv v) ->
                                 y = Val v /\ m \In pinterp (pinv v.+1))}.

Program
Definition pnew : STsep pcnt (emp, fun y i m =>
                                     exists v, y = Val v /\ m \In pinterp (pinv v 0)) :=
  Do (x <-- alloc 0;
      ret (@PCount (fun v r => r = Rep x v)
                    (Do (y <-- !x;
                        x ::= y.+1;;
                        ret y)))).
Next Obligation.
case/swp: {H0} (H0 (Rep x H) (refl_equal _))=>->; heval=>D w.
move/(_ (Rep x w) (refl_equal _)); case/opn=>D1; heap_cancel=>//= _ _ ->.
by split=>//= r ->; auto.
Qed.
Next Obligation.
case: H=><-; apply: bnd_alloc=>// x; heval=>D; hhauto; rewrite InE unh0 in D *.
move=>r -> /=; auto.
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

