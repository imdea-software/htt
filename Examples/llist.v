
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From fcsl Require Import axioms pred.
From fcsl Require Import pcm unionmap heap auto autopcm automap.
From HTT Require Import model heapauto.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Obligation Tactic := auto.

(* Linked lists, storing a value and next pointer in consecutive locations. *)
(* We start with a more general "segment" definition, where the last node's *)
(* next pointer is an arbitrary q *)

Fixpoint lseg {A} (p q : ptr) (xs : seq A) :=
  if xs is hd::tl then
    [Pred h | exists r h',
       h = p :-> hd \+ (p .+ 1 :-> r \+ h') /\ h' \In lseg r q tl]
  else [Pred h | p = q /\ h = Unit].

Definition EmptyList : exn := exn_from_nat 15.

Section LSeg.
Variable A : Type.

(* appending a value to the list segment *)

Lemma lseg_rcons (xs : seq A) x p r h :
        h \In lseg p r (rcons xs x) <->
        exists q h', h = h' \+ (q :-> x \+ q .+ 1 :-> r) /\ h' \In lseg p q xs.
Proof.
move: xs x p r h; elim=>[|x xs IH] y p r h /=.
- by split; case=>x [h'][->][<- ->]; [exists p | exists r]; hhauto.
split.
- case=>z [h1][->]; case/IH=>w [h2][->] H1.
  by exists w, (p :-> x \+ (p .+ 1 :-> z \+ h2)); hhauto.
case=>q [h1][->][z][h2][->] H1.
exists z, (h2 \+ q :-> y \+ q .+ 1 :-> r).
by rewrite -!joinA; split=>//; apply/IH; eauto.
Qed.

(* null pointer represents an empty segment *)

Lemma lseg_null (xs : seq A) q h :
        valid h -> h \In lseg null q xs ->
        [/\ q = null, xs = [::] & h = Unit].
Proof.
case: xs=>[|x xs] D /= H; first by case: H=><- ->.
case: H D=>r [h'][->] _; rewrite validPtUn; hhauto.
Qed.

(* empty heap represents an empty segment *)

Lemma lseg_empty (xs : seq A) p q : Unit \In lseg p q xs -> p = q /\ xs = [::].
Proof.
by case: xs=>[|x xs][] // r [h][/esym/join0E][/unitbE]; rewrite /heap_pts ptsU um_unitbU.
Qed.

(* reformulation of the specification *)

Lemma lseg_case (xs : seq A) p q h :
        h \In lseg p q xs ->
        [/\ p = q, xs = [::] & h = Unit] \/
        exists x r h',
          [/\ xs = x :: behead xs,
              h = p :-> x \+ (p .+ 1 :-> r \+ h') &
              h' \In lseg r q (behead xs)].
Proof.
case: xs=>[|x xs] /=; first by case=>->->; left.
by case=>r [h'][->] H; right; hhauto.
Qed.

(* non-trivial segment represents a non-empty list *)

Corollary lseg_neq (xs : seq A) p q h :
        p != q -> h \In lseg p q xs ->
        exists x r h',
         [/\ xs = x :: behead xs,
             h = p :-> x \+ (p .+ 1 :-> r \+ h') &
             h' \In lseg r q (behead xs)].
Proof.
move=>H /lseg_case; case=>//; case=>E.
by rewrite E eq_refl in H.
Qed.

(* splitting the list corresponds to splitting the heap *)

Lemma lseg_cat (xs ys : seq A) p q h :
        h \In lseg p q (xs++ys) <->
          exists j, h \In lseg p j xs # lseg j q ys.
Proof.
elim: xs h p=>/=.
- move=>h p; split; first by move=>H; exists p, Unit, h; rewrite unitL.
  by case=>j[_][h2][{h}-> [->->]]; rewrite unitL.
move=>x xs IH h p; split.
- case=>r[_][{h}-> /IH][j][h1][h2][-> H1 H2].
  exists j, (p :-> x \+ p.+ 1 :-> r \+ h1), h2; rewrite !joinA; split=>//.
  by exists r, h1; rewrite joinA.
case=>j[_][h2][{h}-> [r][h1][-> H1 H2]].
exists r, (h1 \+ h2); rewrite !joinA; split=>//.
by apply/IH; exists j, h1, h2.
Qed.

End LSeg.

(* Special case when q = null, i.e. the list is self-contained *)
Definition lseq {A} p (xs : seq A) := lseg p null xs.

Section LList.
Variable (A : Type).

(* specializing the null and neq lemmas *)

Lemma lseq_null (xs : seq A) h :
        valid h -> h \In lseq null xs -> xs = [::] /\ h = Unit.
Proof. by move=>D; case/(lseg_null D)=>_ ->. Qed.

Lemma lseq_pos (xs : seq A) p h :
        p != null -> h \In lseq p xs ->
        exists x r h',
          [/\ xs = x :: behead xs,
              h = p :-> x \+ (p .+ 1 :-> r \+ h') &
              h' \In lseq r (behead xs)].
Proof. by apply: lseg_neq. Qed.

(* a valid heap cannot match two different specs *)

Lemma lseq_func (l1 l2 : seq A) p h :
        valid h -> h \In lseq p l1 -> h \In lseq p l2 -> l1 = l2.
Proof.
elim: l1 l2 p h => [|x1 xt IH] /= l2 p h V.
- by case=>->->; case/lseq_null.
case=>q1 /= [h1][E] H; rewrite {}E in H V *.
case/(lseq_pos (defPt_nullO V))=>x2 [q2][h2][->] /=.
do 2![case/(cancel V)=>/dynE/jmE<-{}V].
by move=><- /(IH (behead l2) _ _ V H)=>->.
Qed.

(* main methods *)

(* prepending a value *)

Program Definition insert p (x : A) :
  {l}, STsep (lseq p l, [vfun p' => lseq p' (x::l)]) :=
  Do (q <-- allocb p 2;
      q ::= x;;
      ret q).
Next Obligation.
(* pull out ghost var + precondition, run the first step *)
move=>p x [l][] i /= H; step=>q.
(* run the last 2 steps, guess the final pointer and heap from the goal *)
rewrite unitR -joinA; heval.
Qed.

(* getting the head element *)
(* an example of a partial program, doesn't modify the heap *)

Program Definition head p :
  {l}, STsep (lseq p l,
              fun (y : ans A) h => h \In lseq p l /\
                match y with Val v => l = v :: behead l
                           | Exn e => e = EmptyList /\ l = [::] end) :=
  Do (if p == null then throw EmptyList
        else v <-- !p;
             ret v).
Next Obligation.
(* pull out ghost + precondition, branch *)
move=>p [l][] i /= H; case: ifP H=>[/eqP-> H|/negbT Hp].
- (* there is no head element, abort *)
  step=>V; do!split=>//.
  (* the only non-trivial goal is the list being empty *)
  by case/lseq_null: H.
(* deconstruct non-empty list, run the rest *)
case/(lseq_pos Hp)=>v [r][h1][E {i}-> H1].
by do 2![step]=>_; split=>//; rewrite E; hhauto.
Qed.

(* removing the head element, no-op for an empty list *)

Program Definition remove p :
  {xs : seq A}, STsep (lseq p xs, [vfun p' => lseq p' (behead xs)]) :=
  Do (if p == null then ret p
      else pnext <-- !(p .+ 1);
           dealloc p;;
           dealloc p .+ 1;;
           ret pnext).
Next Obligation.
(* pull out ghost + precondition, branch *)
move=>p [xs][] i /= H; case: ifP H=>[/eqP-> H|/negbT Ep].
- (* the list must be empty *)
  by step=>V; case/lseq_null: H=>//->->.
(* deconstruct non-empty list, run the rest *)
case/(lseq_pos Ep)=>x [q][h][-> {i}-> /= H1].
by heval; rewrite 2!unitL.
Qed.

(* calculating the list length *)

(* the loop invariant: *)
(* 1. heap is unchanged *)
(* 2. total length is accumulator + the length of unprocessed list *)
Definition lenT : Type := forall (pl : ptr * nat),
  {xs : seq A}, STsep (lseq pl.1 xs,
                      [vfun l h => l == pl.2 + length xs /\ lseq pl.1 xs h]).

Program Definition len p :
  {xs : seq A}, STsep (lseq p xs,
                      [vfun l h => l == length xs /\ lseq p xs h]) :=
  Do (let: len := Fix (fun (go : lenT) '(p, l) =>
                        Do (if p == null then ret l
                            else pnext <-- !(p .+ 1);
                                 go (pnext, l + 1)))
      in len (p, 0)).
(* first, the loop *)
Next Obligation.
(* pull out ghosts+precondition, branch *)
move=>_ go _ p l /= _ [xs][] i /= H; case: eqP H=>[->|/eqP Ep] H.
- (* the end is reached *)
  by step=>V; case/(lseq_null V): H=>->->/=; rewrite addn0.
(* deconstruct non-empty list, run one step *)
case/lseq_pos: H=>// x0 [r][h'][-> {i}-> /= H1]; step.
apply: [gX (behead xs)]@h'=>//= _ h2 [/eqP -> Hl] /= _.
rewrite -addnA add1n; eauto.
Qed.
Next Obligation.
(* pull out the ghost var and immediately feed it to the loop *)
by move=>/= p [xs []] i /= H; apply: [gE xs].
Qed.

(* concatenation: modifies the first list, returning nothing *)

(* the loop invariant: *)
(* the first list should not be empty and not overlap the second *)
Definition catT (p2 : ptr) : Type :=
  forall (p1 : ptr), {xs1 xs2 : seq A},
    STsep (fun h => p1 != null /\ (lseq p1 xs1 # lseq p2 xs2) h,
           [vfun _ : unit => lseq p1 (xs1 ++ xs2)]).

Program Definition concat p1 p2 :
  {xs1 xs2 : seq A}, STsep (lseq p1 xs1 # lseq p2 xs2,
                           [vfun a => lseq a (xs1 ++ xs2)]) :=
  Do (let: cat := Fix (fun (go : catT p2) q =>
                        Do (next <-- !(q .+ 1);
                            if (next : ptr) == null
                               then q .+ 1 ::= p2;;
                                    ret tt
                               else go next))
      in if p1 == null
           then ret p2
           else cat p1;;
                ret p1).
(* first, the loop *)
Next Obligation.
(* pull out ghosts + preconditions *)
move=>_ p2 go q [xs1][xs2][] _ /= [Hq][i1][i2][-> H1 H2].
(* deconstruct the first non-empty list, branch *)
case/(lseq_pos Hq): H1=>x [r][i][E {i1}-> H1]; step.
case: ifP H1=>[/eqP ->{r}|/negbT N] H1.
- (* we've reached the last node of the first list *)
  (* make it point to the second list *)
  do 2![step]=>V.
  (* the remaining heap for the first list is empty *)
  case/(lseq_null (validX V)): H1 E=>/=->->->/=.
  (* the rest is just the second list *)
  by rewrite unitR -joinA; eauto.
(* feed new ghosts and subheap to the recursive call *)
(* we use a generalized ghost autolemma here *)
apply: [gX (behead xs1), xs2]@(i \+ i2)=>//= _.
- (* the tail is not null so the precondition is satisfied *)
  by split=>//; vauto.
(* assemble the concatenation from head and tail *)
by move=>m H _; rewrite E /=; eauto.
Qed.
(* next, the initial call *)
Next Obligation.
(* pull out ghosts + preconditions, branch *)
move=>p1 p2 [xs1][xs2][] /= _ [i1][i2][-> H1 H2].
case: ifP H1=>[/eqP ->|/negbT N] H1.
- (* first list is empty, the result simplifies to the second list *)
  by step=>V; case/(lseq_null (validL V)): H1=>->->; rewrite unitL.
(* otherwise, feed everything to the loop *)
by apply: [stepE xs1, xs2]=>[|[] //= [] m Hm]; heval.
Qed.

(* in-place reversal by pointer swinging *)

(* the loop invariant: *)
(* 1. the processed and remaining parts should not overlap *)
(* 2. the result is processed part + a reversal of remainder *)
Definition revT : Type := forall (p : ptr * ptr),
  {i done : seq A}, STsep (lseq p.1 i # lseq p.2 done,
                          [vfun y => lseq y (catrev i done)]).

Program Definition reverse p :
  {xs : seq A}, STsep (lseq p xs, [vfun p' => lseq p' (rev xs)]) :=
  Do (let: reverse := Fix (fun (go : revT) '(i, done) =>
                        Do (if i == null then ret done
                            else next <-- !i .+ 1;
                                 i .+ 1 ::= done;;
                                 go (next, i)))
      in reverse (p, null)).
(* first, the loop *)
Next Obligation.
(* pull out ghosts + preconditions, branch *)
move=>_ go _ i done _ [x1][x2][] _ /= [i1][i2][-> H1 H2].
case: eqP H1=>[->|/eqP E] H1.
- (* nothing left to reverse, return the accumulator *)
  by step=>/validL V1; case/(lseq_null V1): H1=>->->/=; rewrite unitL.
(* deconstruct non-empty remainder *)
case/lseq_pos: H1=>// xd [xn][h'][-> {i1}-> /= H1].
(* swing the pointer, feed shifted ghosts to recursive call *)
do 2!step; apply: [gE (behead x1), xd::x2]=>//=.
(* rearrange the heap to match context *)
rewrite !(pull h') -!joinA; vauto.
Qed.
Next Obligation.
(* pull out ghost, feed it + empty accumulator to the loop *)
move=>p [xs][] /= i H; apply: [gE xs, [::]]=>//=; exists i; hhauto.
Qed.

Variable B : Type.

(* list mapping, an example of a higher-order function *)

(* the loop invariant: *)
(* the result is a mapped list *)
Definition lmapT (f : A -> B) :=
  forall (p : ptr),
    {xs : seq A}, STsep (lseq p xs,
                        [vfun _ : unit => lseq p (map f xs)]).

Program Definition lmap f : lmapT f :=
  Fix (fun (lmap : lmapT f) p =>
    Do (if p == null
        then ret tt
        else t <-- !p;
             p ::= f t;;
             nxt <-- !p .+ 1;
             lmap nxt)).
Next Obligation.
(* pull out ghost + precondition, branch *)
move=>f lmap p [xs][] h /= H; case: ifP H=>[/eqP ->|/negbT N] H.
- (* the list is empty *)
  by step=>V; case/(lseq_null V): H=>->->.
(* deconstruct non-empty list, run the rest *)
case/(lseq_pos N): H=>t [nxt][h'][-> {h}-> /= H]; heval.
(* feed the tail as a ghost var + subheap to recursive call *)
apply/[gX (behead xs)]@h'=>//= _ h2 Q V'; eauto.
Qed.

End LList.

Arguments head {A} p.
Arguments remove {A} p.
