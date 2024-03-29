From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype seq.
From pcm Require Import options axioms pred.
From pcm Require Import pcm unionmap heap autopcm.
From htt Require Import model heapauto.
From htt Require Import llist.

Definition stack (T : Type) := ptr.
Definition EmptyStack := exn_from_nat 25.

Module Stack.
Section Stack.
Variable T : Type.
Notation stack := (stack T).

Opaque insert head remove.

(* a stack is just a pointer to a singly-linked list *)
Definition shape s (xs : seq T) :=
  [Pred h | exists p h', [ /\ valid (s :-> p \+ h'),
                              h = s :-> p \+ h' &
                              h' \In lseq p xs]].

(* a heap cannot match two different specs *)
Lemma shape_inv : forall s xs1 xs2 h,
        h \In shape s xs1 -> h \In shape s xs2 -> xs1 = xs2.
Proof.
move=>s xs1 xs2 _ [p][h1][D -> S][p2][h2][D2].
case/(cancelO _ D)=><- _; rewrite !unitL=><-.
by apply: lseq_func=>//; move/validR: D.
Qed.

(* well-formed stack is a valid heap *)

Lemma shapeD s xs : forall h, h \In shape s xs -> valid h.
Proof. by move=>h [p][h'][D ->]. Qed.

(* main methods *)

(* new stack is a pointer to an empty heap/list *)

Program Definition new : STsep (emp, [vfun y => shape y [::]]) :=
  Do (alloc null).
Next Obligation. by move=>/= [] i ?; step=>??; vauto. Qed.

(* freeing a stack, possible only when it's empty *)

Program Definition free s : STsep (shape s [::],
                                   [vfun _ h => h = Unit]) :=
  Do (dealloc s).
Next Obligation.
by move=>s [] ? /= [?][?][V -> [_ ->]]; step=>_; rewrite unitR.
Qed.

(* pushing to the stack is inserting into the list and updating the pointer *)

Program Definition push s x : {xs}, STsep (shape s xs,
                                          [vfun _ => shape s (x :: xs)]) :=
  Do (l <-- !s;
      l' <-- insert l x;
      s ::= l').
Next Obligation.
(* pull out ghost + precondition, get the list *)
move=>s x [xs][] _ /= [l][h][V -> H]; step.
(* run the insert procedure with the ghost, deconstruct the new list *)
apply: [stepX xs]@h=>//= x0 _ [r][h'][-> H'].
(* store the new list *)
by step=>V'; hhauto.
Qed.

(* popping from the stack is: *)
(* 1. trying to get the head *)
(* 2. removing it from the list and updating the pointer on success *)

Program Definition pop s :
  {xs}, STsep (shape s xs,
               fun y h => shape s (behead xs) h /\
                 match y with Val v => xs = v :: behead xs
                            | Exn e => e = EmptyStack /\ xs = [::] end) :=
  Do (l <-- !s;
      try (head l)
        (fun x =>
          l' <-- @remove T l;
          s ::= l';;
          ret x)
        (fun _ => throw EmptyStack)).
Next Obligation.
(* pull out ghost vars and precondition *)
move=>s [xs][] _ /= [p][h0][V -> H].
(* get the list and invoke head on it, deal with exception first *)
step; apply/[tryX xs]@h0=>//= [x|ex] m [Hm]; last first.
- (* throw the stack exception *)
  case=>{ex}_ E /=; step=>Vm; split=>//.
  by rewrite E /= in Hm *; vauto.
(* invoke remove and run the rest of the program *)
move=>E; apply: [stepX xs]@m=>//= p' m' H'.
by do 2![step]=>V'; split=>//; vauto.
Qed.

End Stack.
End Stack.
