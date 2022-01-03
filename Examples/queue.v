From mathcomp Require Import ssreflect ssrbool ssrfun eqtype seq.
From fcsl Require Import axioms pred.
From fcsl Require Import pcm unionmap heap.
From HTT Require Import domain heap_extra model heapauto.
From HTT Require Import llistR.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Obligation Tactic := auto.

Record queue (T : Type) : Type := Queue {front: ptr; back: ptr}.
Definition EmptyQueue : exn := exn_from_nat 100.

Module Queue.
Section Queue.
Variable T : Type.
Notation queue := (queue T).

Definition is_queue (fr bq : ptr) (xs : seq T) :=
  if fr == null then [Pred h | [/\ bq = null, xs = [::] & h = Unit]]
  else [Pred h | exists xt x h',
        [/\ xs = rcons xt x,
            valid (bq :-> x \+ (bq .+ 1 :-> null \+ h')),
                  (bq :-> x \+ (bq .+ 1 :-> null \+ h')) = h
          & h' \In lseg fr bq xt]].

Definition shape (q : queue) (xs : seq T) :=
  [Pred h | exists fr bq h',
    [/\ valid (front q :-> fr \+ (back q :-> bq \+ h')),
              (front q :-> fr \+ (back q :-> bq \+ h')) = h &
              h' \In is_queue fr bq xs]].

Lemma is_queue_nil fr bq h :
        h \In is_queue fr bq [::] -> [/\ fr = null, bq = null & h = Unit].
Proof.
by rewrite /is_queue; case: eqP =>[->[->]_->| N [[|y xt]][x][h'][]].
Qed.

Lemma is_queue_add_last fr bq xt x h :
         (exists h', [/\ valid (bq :-> x \+ (bq .+ 1 :-> null \+ h')),
                                bq :-> x \+ (bq .+ 1 :-> null \+ h') = h &
                                h' \In lseg fr bq xt]) ->
         h \In is_queue fr bq (rcons xt x).
Proof.
rewrite /is_queue =>[[h']][D] <- H.
case: eqP H=>[->|_ H].
- move: D=>/[dup]/validR/validR D0 /[swap].
  by case/lseg_null=>//->->->; rewrite validPtUn.
by exists xt, x, h'.
Qed.

Lemma backfront fr bq xs h :
        h \In is_queue fr bq xs -> (fr == null) = (bq == null).
Proof.
rewrite /is_queue; case: ifP=>[E [->]_ _| E [xt][x][h'][_] D] //.
by case: eqP D=>// ->; rewrite validPtUn.
Qed.

Lemma shapeD q xs : forall h, h \In shape q xs -> valid h. (* proper *)
Proof. by move=>h [h1] [bq][h'] [] D <-. Qed.

Program Definition new :
          STsep (emp, [vfun v => shape v [::]]) :=
  Do (x <-- alloc null;
      y <-- alloc null;
      ret (Queue T x y)).
Next Obligation.
move=>[] _ /= ->.
step=>x; step=>y; step=>V.
exists null, null, Unit.
by rewrite !unitR in V *; rewrite joinC.
Qed.

Program Definition free (q : queue) :
          STsep (shape q [::], [vfun _ h => h = Unit]) :=
  Do (dealloc (front q);;
      dealloc (back q)).
Next Obligation.
move=>q [] _ /= [fr][bq][h][/[swap]<-/[swap]].
case/is_queue_nil=>->->->; rewrite unitR=>V.
by step; step=>_; rewrite unitR.
Qed.

Program Definition enq (q : queue) (x : T) :
  {xs}, STsep (shape q xs,
               [vfun _ => shape q (rcons xs x)]) :=
  Do (next <-- allocb null 2;
      next ::= x;;
      ba <-- !back q;
      back q ::= next;;
      (if (ba : ptr) == null
         then front q
         else ba .+ 1) ::= next).
Next Obligation.
move=>q x [xs][] _ /= [fr][bq][h'][D <- H].
step=>next; step.
(* TODO do 2!step *)
apply: (bnd_readR (x:=back q))=>/=.
apply: (bnd_writeR (x:=back q))=>/=.
rewrite -(backfront H) unitR.
case: ifP H=>Ef; rewrite /is_queue ?Ef.
- case=>_->->.
  (* TODO step *)
  apply: (val_writeR (x:=front q))=>/=.
  rewrite unitR=>V.
  exists next, next, (next :-> x \+ next .+ 1 :-> null).
  rewrite joinA joinC; split=>//.
  apply: (@is_queue_add_last _ _ [::]).
  exists Unit; rewrite unitR; split=>//.
  by exact: (validL V).
case=>s2[x2][i2][->] {}D <- H2.
(* TODO step *)
apply: (val_writeR (x:=bq.+1))=>/=.
rewrite joinC !joinA=>V.
exists fr, next, (bq :-> x2 \+ bq .+ 1 :-> next \+ i2 \+ next :-> x \+ next .+ 1 :-> null).
rewrite !joinA; split=>//.
apply: is_queue_add_last.
exists (bq :-> x2 \+ bq .+ 1 :-> next \+ i2).
rewrite joinA joinC.
rewrite -!joinA in V; move/validR/validR: V=>V.
rewrite -2!joinA; split=>//; first by rewrite !joinA.
by apply/lseg_add_last; exists bq, i2; rewrite joinC.
Qed.

Program Definition deq (q : queue) :
  {xs}, STsep (shape q xs,
               fun y h => shape q (behead xs) h /\
                 if y is Val v
                   then xs = v :: behead xs
                   else y = Exn EmptyQueue /\ xs = [::]) :=
  Do (fr <-- !front q;
      if (fr : ptr) == null then throw _ EmptyQueue
      else
        x <-- !fr;
        next <-- !fr .+ 1;
        front q ::= next;;
        dealloc fr;;
        dealloc fr .+ 1;;
        if (next : ptr) == null
          then back q ::= null;;
               ret x
        else ret x).
Next Obligation. by []. Qed.
Next Obligation.
move=>q [xs][] _ /= [fr][bq][h][D <- H].
step; case: ifP H=>Ef; rewrite /is_queue Ef.
(* TODO: val_throwR should be enlinked into the automation *)
(* so that we can just do step here as well *)
(* insted of apply: val_throwR *)
- case=>->->->/=; apply: val_throwR=>V; split=>//.
  exists fr, null, Unit; rewrite unitR in V *; split=>//.
  by rewrite Ef.
case=>[[|y xt]][x][h'][->] {}D {h}<- /=.
- case=>->->; do !step; rewrite !unitR=>V; split=>//.
  by exists null, null, Unit; rewrite unitR.
case=>next [h2][->] H; do !step; rewrite !unitL. 
case: ifP H=>[/eqP ->|N] H.
- rewrite !(pull h2); do ![step]=>V2; case/(lseg_null (validL V2)): H D=>->->->. 
  by rewrite validPtUn. (* TODO: validX should obviate the rewrite by validPtUn *)
step=>V; split=>//; exists next, bq, (bq :-> x \+ (bq .+ 1 :-> null \+ h2)).
by rewrite N; split=>//; exists xt, x, h2; split=>//; move/validR/validR: V.
(* TODO: validX should be used instead of validR/validR *)
Qed.

End Queue.
End Queue.
