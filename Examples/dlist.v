
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From fcsl Require Import axioms pred.
From fcsl Require Import pcm unionmap heap automap.
From HTT Require Import domain model heapauto.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Obligation Tactic := auto.

(* doubly linked lists *)

(* preceding node, first node, last node, succeeding node *)
Fixpoint dseg {A} (pp p q qn : ptr) (xs : seq A) :=
  if xs is hd::tl then
    [Pred h | exists r h',
                 h = p :-> hd \+ (p.+ 1 :-> r \+ (p.+ 2:-> pp \+ h'))
              /\ h' \In dseg p r q qn tl]
  else [Pred h | [/\ p = qn, pp = q & h = Unit]].

Section DSeg.
Variable A : Type.

Lemma dseg_rcons (xs : seq A) x pp p q qn h :
        h \In dseg pp p q qn (rcons xs x) <->
        exists r h',
           h = h' \+ (q :-> x \+ (q.+ 1 :-> qn \+ q.+ 2 :-> r))
        /\ h' \In dseg pp p r q xs.
Proof.
elim: xs pp p h => [|y xs IH] pp p h/=.
- split; case=>r[h'][-> [->->->]]; rewrite ?unitR ?unitL.
  - by exists pp, Unit; rewrite unitL.
  by exists qn, Unit; rewrite unitR.
split.
- case=>r[_][-> /IH][s][h'][-> H'].
  exists s, (p :-> y \+ (p.+ 1 :-> r \+ (p.+ 2 :-> pp \+ h'))).
  rewrite !joinA; split=>//.
  by exists r, h'; rewrite !joinA.
case=>r[_][->][s][h'][-> H'].
exists s, (h' \+ (q :-> x \+ (q.+ 1 :-> qn \+ q.+ 2 :-> r))).
rewrite !joinA; split=>//; apply/IH.
by exists r, h'; rewrite !joinA.
Qed.

Lemma dseg_nullL (xs : seq A) pp q qn h :
        valid h -> h \In dseg pp null q qn xs ->
        [/\ qn = null, pp = q, xs = [::] & h = Unit].
Proof.
case: xs=>[|x xs] /= D H; first by case: H.
by case: H D=>r[h'][-> _]; rewrite validPtUn eq_refl.
Qed.

Lemma dseg_nullR (xs : seq A) pp p qn h :
        valid h -> h \In dseg pp p null qn xs ->
        [/\ p = qn, pp = null, xs = [::] & h = Unit].
Proof.
case/lastP: xs=>[|xs x] D /=; first by case.
case/dseg_rcons=>r[h'][]; move: D=>/[swap]->/validR.
by rewrite validPtUn.
Qed.

Lemma dseg_neqL (xs : seq A) (pp p q qn : ptr) h :
        p != qn -> h \In dseg pp p q qn xs ->
        exists x r h',
         [/\ xs = x :: behead xs,
             p :-> x \+ (p.+ 1 :-> r \+ (p.+ 2 :-> pp \+ h')) = h &
             h' \In dseg p r q qn (behead xs)].
Proof.
case: xs=>[|x xs] /= H; last first.
- by case=>r[h'][-> H']; exists x, r, h'.
by case=>E; rewrite E eq_refl in H.
Qed.

Lemma dseg_neqR (xs : seq A) (pp p q qn : ptr) h :
        pp != q -> h \In dseg pp p q qn xs ->
        exists s x r h',
         [/\ xs = rcons s x,
             h' \+ (q :-> x \+ (q.+ 1 :-> qn \+ q.+ 2 :-> r)) = h &
             h' \In dseg pp p r q s].
Proof.
case/lastP: xs=>[|xs x] /= H.
- by case=>_ E; rewrite E eq_refl in H.
case/dseg_rcons=>r[h'][{h}-> H'].
by exists xs, x, r, h'.
Qed.

Lemma dseg_cat (xs ys : seq A) pp p q qn h :
        h \In dseg pp p q qn (xs++ys) <->
          exists jn j, h \In dseg pp p j jn xs # dseg j jn q qn ys.
Proof.
elim: xs pp p h=>/=.
- move=>pp p h; split; first by move=>H; exists p, pp, Unit, h; rewrite unitL.
  by case=>jn [j][h1][h2][{h}-> [->->->]]; rewrite unitL.
move=>x xs IH pp p h; split.
- case=>r [_][{h}-> /IH][jn][j][h1][h2][-> H1 H2].
  exists jn, j, (p :-> x \+ p.+ 1 :-> r \+ p.+ 2 :-> pp \+ h1), h2.
  by rewrite !joinA; split=>//; exists r, h1; rewrite !joinA.
case=>jn[j][_][h2][{h}->][r][h1][-> H1 H2].
exists r, (h1 \+ h2); rewrite !joinA; split=>//.
by apply/IH; exists jn, j, h1, h2.
Qed.

End DSeg.

(* Special case when pp = null and qn = null *)
Definition dseq {A} p q (xs : seq A) := dseg null p q null xs.

Section DList.
Variable A : Type.

Lemma dseq_nullL (xs : seq A) q h :
        valid h -> h \In dseq null q xs ->
        [/\ q = null, xs = [::] & h = Unit].
Proof. by move=>D; case/(dseg_nullL D). Qed.

Lemma dseq_nullR (xs : seq A) p h :
        valid h -> h \In dseq p null xs ->
        [/\ p = null, xs = [::] & h = Unit].
Proof. by move=>D; case/(dseg_nullR D). Qed.

Lemma dseq_posL (xs : seq A) p q h :
        p != null -> h \In dseq p q xs ->
        exists x r h',
         [/\ xs = x :: behead xs,
             p :-> x \+ (p.+ 1 :-> r \+ (p.+ 2 :-> null \+ h')) = h &
             h' \In dseg p r q null (behead xs)].
Proof. by apply: dseg_neqL. Qed.

Lemma dseq_posR (xs : seq A) p q h :
        q != null -> h \In dseq p q xs ->
        exists s x r h',
          [/\ xs = rcons s x,
              h' \+ (q :-> x \+ (q.+ 1 :-> null \+ q.+ 2 :-> r)) = h &
              h' \In dseg null p r q s].
Proof. by rewrite eq_sym=>Hq /(dseg_neqR Hq). Qed.

(* main methods *)

Program Definition insertL p q (x : A) :
  {l}, STsep (dseq p q l, [vfun pq => dseq pq.1 pq.2 (x::l)]) :=
  Do (r <-- allocb x 3;
      r.+ 1 ::= p;;
      r.+ 2 ::= null;;
      if p == null then ret (r,r)
        else p.+ 2 ::= r;;
             ret (r,q)).
Next Obligation.
move=>p q x [l []] i /= H.
step=>r; rewrite unitR ptrA; do 2!step; case: ifP H.
- move/eqP=>->/dseq_nullL H.
  step; rewrite joinA=>/validR/H [_->->] /=.
  by exists null, Unit; rewrite !joinA.
move/negbT=>Hq /(dseq_posL Hq) [y][z][h'][E {i}<- H'].
do 2![step]=>V.
exists p, (p :-> y \+ (p.+ 1 :-> z \+ (p.+ 2 :-> r \+ h'))).
rewrite !joinA; split=>//; rewrite E /=.
by exists z, h'; rewrite !joinA.
Qed.

Program Definition insertR p q (x : A) :
  {l}, STsep (dseq p q l, [vfun pq => dseq pq.1 pq.2 (rcons l x)]) :=
  Do (r <-- allocb x 3;
      r.+ 1 ::= null;;
      r.+ 2 ::= q;;
      if q == null then ret (r,r)
        else q.+ 1 ::= r;;
             ret (p,r)).
Next Obligation.
move=>p q x [l []] i /= H.
step=>r; rewrite unitR ptrA; do 2!step; case: ifP H.
- move/eqP=>->/dseq_nullR H.
  step; rewrite joinA=>/validR/H [_->->] /=.
  by exists null, Unit; rewrite !joinA.
move/negbT=>Hq /(dseq_posR Hq) [s][y][z][h'][E {i}<- H'].
do 2![step]=>_; apply/dseg_rcons.
exists q, (h' \+ (q :-> y \+ (q.+ 1 :-> r \+ q.+ 2 :-> z))).
split; first by rewrite joinC.
by rewrite {l}E; apply/dseg_rcons; exists z, h'.
Qed.

(* traversing the dlist backwards and consing all elements *)
(* reifies the specification *)

Definition traverse_backT (p : ptr) : Type :=
  forall (qs : ptr * seq A),
  {l nx}, STsep (dseg null p qs.1 nx l,
                [vfun r h => h \In dseg null p qs.1 nx l
                          /\ r = l ++ qs.2]).

Program Definition traverse_back p q :
  {l}, STsep (dseq p q l,
             [vfun r h => h \In dseq p q l /\ r = l]) :=
  Do (let: tb :=
        Fix (fun (go : traverse_backT p) '(r, acc) =>
              Do (if r == null then ret acc
                  else x <-- !r;
                       rnxt <-- !(r.+ 2);
                       go (rnxt, x :: acc)))
      in tb (q, [::])).
Next Obligation.
move=>p _ go [r acc] _ _ [->->][l][nx][] i /= H.
case: ifP H.
- move/eqP=>->/dseg_nullR H.
  by step=>/H [->_->->].
move/negbT; rewrite eq_sym=>Hr /(dseg_neqR Hr) [xs][x][z][h'][E {i}<- H'].
do 2!step; apply: [gR xs, r]@h'=>//= _ m [Hm ->] _; rewrite E /=.
split; last by rewrite -cats1 -catA.
by apply/dseg_rcons; exists z, m.
Qed.
Next Obligation.
move=>p q [xs][] i /= H.
by apply: [gE xs, null]=>//= y m _; rewrite cats0.
Qed.

End DList.
