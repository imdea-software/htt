From mathcomp Require Import ssreflect ssrbool ssrfun eqtype seq.
From fcsl Require Import axioms pred.
From fcsl Require Import pcm unionmap heap.
From HTT Require Import domain heap_extra model heapauto.
From HTT Require Import llistR.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Obligation Tactic := auto.

Definition stack (T : Type) := ptr.
Definition EmptyStack := exn_from_nat 25.

Module Stack.
Section Stack.
Variable T : Type.
Notation stack := (stack T).

Definition shape s (xs : seq T) := [Pred h | exists p h', valid (s :-> p \+ h') /\
                                    s :-> p \+ h' = h /\ h' \In lseq p xs].

Lemma shape_inv : forall s xs1 xs2 h, h \In shape s xs1 -> h \In shape s xs2 -> xs1 = xs2.
Proof.
move=>s xs1 xs2 _ [p][h][D][<-] S [p2][h2][D2][].
case/(cancelO _ D2)=>-> _; rewrite !unitL=>->.
by apply: lseq_func=>//; move/validR: D.
Qed.

Program Definition new : STsep (emp, [vfun y => shape y [::]]) :=
  Do (alloc null).
Next Obligation. by move=>/= [] i ?; step=>??; exists null, i. Qed.

Program Definition free s : STsep (shape s [::],
                                   [vfun _ h => h = Unit]) :=
  Do (dealloc s).
Next Obligation.
move=>s [] _ /= [?][?][V][<-][E E0]; step=>_.
by rewrite E0 unitR.
Qed.

Program Definition push s x : {xs}, STsep (shape s xs,
                                          [vfun _ => shape s (x :: xs)]) :=
  Do (hd <-- !s;
      nd <-- allocb x 2;
      nd .+ 1 ::= (hd : ptr);;
      s ::= nd).
Next Obligation.
move=>s x [xs][] _ /= [p][h0][V][<- H].
do 2![step]=>p2; do 2!step.
rewrite unitR=>V2.
rewrite joinC joinA in V2 *.
exists p2, (h0 \+ p2 :-> x \+ p2 .+ 1 :-> p).
rewrite !joinA; do!split=>//.
exists p, h0; split=>//.
by rewrite -joinA joinC joinA.
Qed.

Program Definition pop s :
  {xs}, STsep (shape s xs,
               fun y h => shape s (behead xs) h /\
                 match y with Val v => xs = v :: behead xs
                            | Exn e => e = EmptyStack /\ xs = [::] end) :=
  Do (hd <-- !s;
      if (hd : ptr) == null then throw EmptyStack
      else
        x <-- !hd;
        next <-- !(hd .+ 1);
        dealloc hd;;
        dealloc hd .+ 1;;
        s ::= (next : ptr);;
        ret x).
Next Obligation.
move=>s [xs][] _ /= [p][h0][V][<- H].
step; case: eqP.
- move=>Ep; step=>_.
  rewrite Ep in H V *; case: (lseq_null (validR V) H)=>->?/=.
  by split=>//; exists null, h0.
move/eqP=>Ep.
case: (lseq_pos Ep H)=>/= x[r][h1][E1]E0 H1; rewrite -{}E0 in H *.
do 6!step; rewrite !unitL=>V1.
by split=>//; exists r, h1.
Qed.

End Stack.
End Stack.
