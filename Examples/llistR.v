
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From fcsl Require Import axioms pred.
From fcsl Require Import pcm unionmap heap automap.
From HTT Require Import domain heap_extra model heapauto.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Obligation Tactic := auto.

(* linked lists, storing a value and next pointer in consecutive locations *)

Fixpoint lseg {A} (p q : ptr) (xs : seq A) :=
  if xs is hd::tl then
    [Pred h | exists r h',
       h = p :-> hd \+ (p .+ 1 :-> r \+ h') /\ h' \In lseg r q tl]
  else [Pred h | p = q /\ h = Unit].

Section LSeg.
Variable A : Type.

Lemma lseg_add_last (xs : seq A) x p r h :
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

Lemma lseg_null (xs : seq A) q h :
         valid h -> h \In lseg null q xs ->
         [/\ q = null, xs = [::] & h = Unit].
Proof.
case: xs=>[|x xs] D /= H; first by case: H=><- ->.
case: H D=>r [h'][->] _; rewrite validPtUn; hhauto.
Qed.

Lemma lseg_neq (xs : seq A) p q h :
        p != q -> h \In lseg p q xs ->
        exists x r h',
         [/\ xs = x :: behead xs, p :-> x \+ (p .+ 1 :-> r \+ h') = h &
             h' \In lseg r q (behead xs)].
Proof.
case: xs=>[|x xs] /= H []; last by move=>y [h'][->] H1; hhauto.
by move=>E; rewrite E eq_refl in H.
Qed.

Lemma lseg_empty (xs : seq A) p q : Unit \In lseg p q xs -> p = q /\ xs = [::].
Proof.
by case: xs=>[|x xs][] // r [h][/esym/join0E][/unitbE]; rewrite /heap_pts ptsU um_unitbU.
Qed.

Lemma lseg_case (xs : seq A) p q h :
        h \In lseg p q xs ->
        [/\ p = q, xs = [::] & h = Unit] \/
        exists x r h',
          [/\ xs = x :: behead xs, h = p :-> x \+ (p .+ 1 :-> r \+ h') &
              h' \In lseg r q (behead xs)].
Proof.
case: xs=>[|x xs] /=; first by case=>->->; left.
by case=>r [h'][->] H; right; hhauto.
Qed.

End LSeg.

(* Special case when p = null *)
Definition lseq {A} p (xs : seq A) := lseg p null xs.

Section LList.
Variable A : Type.

Lemma lseq_null (xs : seq A) h : valid h -> h \In lseq null xs -> xs = [::] /\ h = Unit.
Proof. by move=>D; case/(lseg_null D)=>_ ->. Qed.

Lemma lseq_pos (xs : seq A) p h :
        p != null -> h \In lseq p xs ->
        exists x r h',
          [/\ xs = x :: behead xs,
              p :-> x \+ (p .+ 1 :-> r \+ h') = h & h' \In lseq r (behead xs)].
Proof. by apply: lseg_neq. Qed.

Lemma lseq_func (l1 l2 : seq A) p h : valid h -> h \In lseq p l1 -> h \In lseq p l2 -> l1 = l2.
Proof.
elim: l1 l2 p h => [|x1 xt IH] /= l2 p h V.
- by case=>->->; case/lseq_null.
case=>q1 /=[h1][E] H; rewrite {}E in H V *.
case/(lseq_pos (defPt_nullO V))=>x2 [q2][h2][->] /= /esym.
do 2![case/(cancel V)=>/dynE/jmE<-{}V].
by move=><- /(IH (behead l2) _ _ V H)=>->.
Qed.

(* main methods *)

(* prepending *)
Program Definition insert p (x : A) :
  {l}, STsep (lseq p l, [vfun p' => lseq p' (x::l)]) :=
  Do (q <-- allocb p 2;
      q ::= x;;
      ret q).
Next Obligation.
move=>p x [l []] i /= H; step=>q.
by rewrite unitR -joinA; heval.
Qed.

(* removing *)

Program Definition remove p :
  {xs : seq A}, STsep (lseq p xs, [vfun p' => lseq p' (behead xs)]) :=
  Do (if p == null then ret p
      else pnext <-- !(p .+ 1);
           dealloc p;;
           dealloc p .+ 1;;
           ret pnext).
Next Obligation.
move=>p [xs []] i /= H; apply: vrfV=>V; case: ifP H=>H1.
- by rewrite (eqP H1); case/(lseq_null V)=>->->; heval.
case/(lseq_pos (negbT H1))=>x [q][h][->] <- /= H2.
by heval; rewrite 2!unitL.
Qed.

(* length *)

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
Next Obligation.
move=>_ go ? p l /= _ [xs []] i /= H; apply: vrfV=>V.
case: eqP H=>[->|/eqP Hp].
- by case/(lseq_null V)=>->->/=; step; rewrite addn0.
case/lseq_pos=>// x0 [r][h'][->] <- /= H1.
step.
apply: [gR (behead xs)] @ h'=>//= _ h2 [/eqP -> Hl] /= _.
by rewrite -addnA add1n; eauto.
Qed.
Next Obligation. 
by move=>p [xs []] i H; apply: [gE xs].
Qed.

(* concatenation *)

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
Next Obligation.
move=>_ p2 go q [xs1][xs2][_ /= [Hq][i1][i2]][-> H1 H2].
case/(lseq_pos Hq): H1=>x [r][i][E <-{i1} H1]; step.
case: ifP H1=>[/eqP ->{r}|/negbT N] H1.
- do 2![step]=>V.
  case/(lseq_null (validX V)): H1 E=>/=->->->/=.
  by rewrite unitR -joinA; exists p2, i2.
rewrite -!joinA.
apply: [gR (behead xs1), xs2] @ (i \+ i2)=>//=. 
- by split=>//; exists i, i2.
by case=>m ??; rewrite E /=; exists r, m.
Qed.
Next Obligation.
move=>p1 p2 [xs1][xs2][/= _ [i1][i2][-> H1 H2]].
case: ifP H1=>[/eqP ->|/negbT N] H1.
- by step=>V; case/(lseq_null (validL V)): H1=>->->; rewrite unitL.
by apply: [stepE xs1, xs2]=>[|[] //= [] m Hm]; heval.
Qed.


(* in-place reversal *)

Definition shape_rev p (s1 s2 : seq A) := [Pred h | h \In lseq p.1 s1 # lseq p.2 s2].

Definition revT : Type := forall p,
  {i done}, STsep (shape_rev p i done, [vfun y => lseq y (catrev i done)]).

Program Definition reverse p :
  {xs : seq A}, STsep (lseq p xs, [vfun p' => lseq p' (rev xs)]) :=
  Do (let: reverse := Fix (fun (go : revT) '(i, done) =>
                        Do (if i == null then ret done
                            else next <-- !i .+ 1;
                                 i .+ 1 ::= done;;
                                 go (next, i)))
      in reverse (p, null)).
Next Obligation.
move=>_ go _ p done _ [x1][x2][] _ /= [i1][i2][-> H1 H2]; apply: vrfV=>V.
case: eqP H1=>[->|E].
- by case/(lseq_null (validL V))=>->->; rewrite unitL; step.
case/lseq_pos=>[|xd [xn][h'][->] <- /= H1]; first by case: eqP.
do 2!step; apply: [gE (behead x1), xd::x2]=>//=.
by rewrite !(pull h') -!joinA; vauto.
Qed.
Next Obligation.
by move=>p [xs][/= i H]; apply: [gE xs, [::]]=>//; exists i; hhauto.
Qed.

Variable B : Type.

(* Type of recursive map *)
Definition lmapT (f : A -> B) :=
  forall (p : ptr),
    {xs : seq A}, STsep (lseq p xs,
                         fun (_ : ans unit) => lseq p (map f xs)).

Program Definition lmap f : lmapT f :=
  Fix (fun (lmap : lmapT f) p =>
    Do (if p == null
        then ret tt
        else t <-- !p;
             p ::= f t;;
             nxt <-- !p .+ 1;
             lmap nxt)).
Next Obligation.
(* Deconstruct the precondition *)
move=>f lmap p [xs][] h /= P; apply: vrfV=>V.

(* Use if-rule *)
case: ifP=>[X|/negbT X].

(* 1. p == null ==> The list is empty. *)
- move/eqP: X=>Z; rewrite {}Z in P *.
  by case: (lseq_null V P)=>->->; heval.

(* 2. p != null ==> The list is non-empty. *)
case/(lseq_pos X): P=>t [nxt][h'][-> <- /= P].
heval.

(* Decompose the list predicate *)
by apply/[gR (behead xs)] @ h'=>//= _ h2 Q V'; exists nxt, h2.
Qed.

End LList.
