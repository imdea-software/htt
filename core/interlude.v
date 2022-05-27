From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat seq eqtype path.
From fcsl Require Import options axioms.

Lemma rcons_nseq {A : Type} n (x : A) :
  rcons (nseq n x) x = nseq n.+1 x.
Proof. by elim: n=>//=n ->. Qed.

Lemma behead_rcons {A : Type} (xs : seq A) (x : A) :
  0 < size xs ->
  behead (rcons xs x) = rcons (behead xs) x.
Proof. by case: xs. Qed.

Lemma mem_split {T : eqType} (x : T) (s : seq T) :
        x \in s -> exists s1 s2, s = s1 ++ [:: x] ++ s2.
Proof.
case/splitP=>s1 s2; exists s1, s2.
by rewrite -cats1 catA.
Qed.

Lemma mem_split_uniq {T : eqType} (x : T) (s : seq T) :
       x \in s -> uniq s ->
         exists s1 s2, s = s1 ++ [:: x] ++ s2 /\
           uniq (s1 ++ s2) /\ x \notin (s1 ++ s2).
Proof.
move=>/[swap] Hu /mem_split [s1 [s2 H]].
exists s1, s2; move: Hu.
by rewrite H uniq_catCA cons_uniq; case/andP.
Qed.

Lemma allrel_in_l {S T : eqType} (r : T -> S -> bool) (xs xs' : seq T) (ys : seq S) :
  xs =i xs' ->
  allrel r xs ys = allrel r xs' ys.
Proof.
by move=>H; rewrite !allrel_allpairsE; apply/eq_all_r/mem_allpairs_dep.
Qed.

Lemma allrel_in_r {S T : eqType} (r : T -> S -> bool) (xs : seq T) (ys ys' : seq S) :
  ys =i ys' ->
  allrel r xs ys = allrel r xs ys'.
Proof.
by move=>H; rewrite !allrel_allpairsE; apply/eq_all_r/mem_allpairs_dep.
Qed.

Lemma allrel_sub_r {S T : eqType} (r : T -> S -> bool) (xs : seq T) (ys ys' : seq S) :
  {subset ys' <= ys} ->
  allrel r xs ys -> allrel r xs ys'.
Proof.
move=>H Ha; apply/allrelP=>x y Hx Hy.
by move/allrelP: Ha; apply=>//; apply: H.
Qed.

Lemma allrel_trans {S : eqType} (xs ys : seq S) z r :
  transitive r ->
  all (r^~ z) xs -> all (r z) ys -> allrel r xs ys.
Proof.
move=>Ht /allP Ha /allP Hp; apply/allrelP=>x y + Hy.
by move/Ha/Ht; apply; apply: Hp.
Qed.

Lemma path_all {S : Type} (xs : seq S) x r :
  transitive r ->
  path r x xs -> all (r x) xs.
Proof. by move=>Ht; rewrite path_sortedE; [case/andP | exact: Ht]. Qed.
