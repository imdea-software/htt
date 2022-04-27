From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype seq.
From fcsl Require Import axioms pred.
From fcsl Require Import pcm unionmap heap automap.
From HTT Require Import model heapauto.
From HTT Require Import llist.
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

(* a queue is specified as a singly-linked list split into an initial segment and a last node *)
Definition is_queue (fr bq : ptr) (xs : seq T) :=
  if fr == null then [Pred h | [/\ bq = null, xs = [::] & h = Unit]]
  else [Pred h | exists xt x h',
                 [/\ xs = rcons xt x,
                     valid (h' \+ (bq :-> x \+ bq .+ 1 :-> null)),
                     h = h' \+ (bq :-> x \+ bq .+ 1 :-> null) &
                     h' \In lseg fr bq xt]].

(* the structure itself is just a pair of pointers to body + last node *)
(* insertion happens at the last node, and removal at the head *)
Definition shape (q : queue) (xs : seq T) :=
  [Pred h | exists fr bq h',
    [/\ valid (front q :-> fr \+ (back q :-> bq \+ h')),
        h = front q :-> fr \+ (back q :-> bq \+ h') &
        h' \In is_queue fr bq xs]].

(* well-formed queue is a valid heap *)

Lemma shapeD q xs h : h \In shape q xs -> valid h.
Proof. by case=>h1[bq][h'] [] D ->. Qed.

(* empty queue is a pair of null pointers *)

Lemma is_queue_nil fr bq h :
        h \In is_queue fr bq [::] -> [/\ fr = null, bq = null & h = Unit].
Proof.
by rewrite /is_queue; case: eqP=>[->[-> _ ->] | _ [[|y xt][x][h'][]]].
Qed.

(* restructuring the specification for combined list *)

Lemma is_queue_rcons fr bq xt x h :
         h \In is_queue fr bq (rcons xt x) <->
         (exists h', [/\ valid (h' \+ (bq :-> x \+ bq .+ 1 :-> null)),
                         h = h' \+ (bq :-> x \+ bq .+ 1 :-> null) &
                         h' \In lseg fr bq xt]).
Proof.
rewrite /is_queue; split.
- case: eqP; first by move=>-> []; case: xt.
  by move=>N [xt'][x'][h'][/rcons_inj [->->] ???]; exists h'.
case=>h' [D -> H]; case: eqP H=>[->|_ H]; last by vauto.
move: (D)=>/[swap]; case/(lseg_null (validL D))=>->->->.
by rewrite unitL validPtUn.
Qed.

(* pointers should agree in a well-formed queue *)

Lemma backfront fr bq xs h :
        h \In is_queue fr bq xs -> (fr == null) = (bq == null).
Proof.
rewrite /is_queue; case: ifP=>[E [->]_ _| E [xt][x][h'][_] D] //.
by case: eqP D=>// -> /validR; rewrite validPtUn.
Qed.

(* main methods *)

(* new queue is a pair of pointers to an empty segment *)

Program Definition new :
          STsep (emp, [vfun v => shape v [::]]) :=
  Do (x <-- alloc null;
      y <-- alloc null;
      ret (Queue T x y)).
Next Obligation.
(* run the complete program *)
move=>[] _ /= ->; step=>x; step=>y; step=>V.
(* massage the heap to fit the postcondition *)
by exists null, null, Unit; rewrite !unitR /= in V *; rewrite joinC.
Qed.

(* freeing a queue, possible only when it's empty *)

Program Definition free (q : queue) :
          STsep (shape q [::], [vfun _ h => h = Unit]) :=
  Do (dealloc (front q);;
      dealloc (back q)).
Next Obligation.
(* pull out ghosts and precondition *)
move=>q [] _ /= [fr][bq][h][/[swap]->/[swap]].
(* both pointers are null *)
case/is_queue_nil=>->->->; rewrite unitR=>V.
(* run the program *)
by do 2![step]=>_; rewrite unitR.
Qed.

(* for enqueue/dequeue we manipulate the underlying segment directly *)

(* enqueuing is adding a node at the end *)

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
(* pull out ghosts + precondition *)
move=>q x [xs][] _ /= [fr][bq][h'][D -> H].
(* create the new last node and change the back pointer *)
step=>next; do 3!step.
(* as the pointers agree, test the front one to reason structurally *)
rewrite -(backfront H) unitR; case: ifP H=>Ef; rewrite /is_queue ?Ef.
- (* the queue was empty, set the front pointer to new node *)
  case=>_->->; step; rewrite unitR=>V.
  (* massage the heap and restructure the goal *)
  exists next, next, (next :-> x \+ next.+ 1 :-> null).
  rewrite joinA joinC; split=>//; apply/(@is_queue_rcons _ _ [::]).
  by exists Unit; rewrite unitL; split=>//; exact: (validL V).
(* the queue wasn't empty, link the new node to the last one *)
case=>s2[x2][i2][->] {}D -> H2; step=>V.
(* massage the heap and simplify the goal *)
exists fr, next, (i2 \+ bq :-> x2 \+ bq.+ 1 :-> next \+ next :-> x \+ next.+ 1 :-> null).
split; first by apply: (validX V).
- by rewrite joinC !joinA.
(* the new node conforms to the queue spec *)
apply/is_queue_rcons; exists (i2 \+ bq :-> x2 \+ bq.+ 1 :-> next).
rewrite joinA; split=>//; first by apply: (validX V).
(* assemble the old queue back *)
by apply/lseg_rcons; exists bq, i2; rewrite joinA.
Qed.

(* dequeuing is removing the head node and adjusting pointers *)

Program Definition deq (q : queue) :
  {xs}, STsep (shape q xs,
               fun y h => shape q (behead xs) h /\
                 match y with Val v => xs = v :: behead xs
                            | Exn e => e = EmptyQueue /\ xs = [::] end) :=
  Do (fr <-- !front q;
      if (fr : ptr) == null then throw EmptyQueue
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
Next Obligation.
(* pull out ghosts + precondition *)
move=>q [xs][] _ /= [fr][bq][h][D -> H].
(* read the list, branch *)
step; case: ifP H=>Ef; rewrite /is_queue Ef.
- (* list is empty, throw an exception *)
  case=>->->->/=; step=>V; split=>//.
  (* massage and simplify *)
  exists fr, null, Unit; rewrite unitR in V *; split=>//.
  by rewrite Ef.
(* deconstruct the initial segment *)
case=>[[|y xt]][x][h'][->] {}D {h}-> /=.
- (* segment is empty, so dequeuing returns the last node *)
  case=>->->; do 7!step; rewrite !unitR=>V; split=>//.
  by exists null, null, Unit; rewrite unitR.
(* segment is non-empty, run up to the branching point *)
case=>next [h2][->] H; do 5!step; rewrite !unitL.
case: ifP H=>[/eqP ->|N] H.
- (* null pointer is in the middle of the segment *)
  do 2![step]=>V2.
  (* this contradicts heap validity *)
  case/(lseg_null (validX V2)): H D=>/=-> _ _ /validR.
  by rewrite validPtUn.
(* return the segment head and simplify *)
step=>V; split=>//; exists next, bq, (h2 \+ (bq :-> x \+ bq .+ 1 :-> null)).
by rewrite N; split=>//; vauto; apply: (validX V).
Qed.

End Queue.
End Queue.
