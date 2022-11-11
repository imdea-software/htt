From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat seq eqtype path.
From pcm Require Import options prelude ordtype.

Lemma implyb_trans a b c : a ==> b -> b ==> c -> a ==> c.
Proof. by case: a=>//=->. Qed.

Section Seq.
Variable (A : Type).

Lemma rcons_nseq n (x : A) :
        rcons (nseq n x) x = nseq n.+1 x.
Proof. by elim: n=>//=n ->. Qed.

Lemma behead_rcons (xs : seq A) x :
        0 < size xs ->
        behead (rcons xs x) = rcons (behead xs) x.
Proof. by case: xs. Qed.

Lemma path_all (xs : seq A) x r :
        transitive r ->
        path r x xs -> all (r x) xs.
Proof. by move=>Ht; rewrite path_sortedE; [case/andP | exact: Ht]. Qed.

Lemma sorted_rconsE (leT : rel A) xs x :
        transitive leT ->
        sorted leT (rcons xs x) = all (leT^~ x) xs && sorted leT xs.
Proof.
move/rev_trans=>Ht; rewrite -(revK (rcons _ _)) rev_rcons rev_sorted /=.
by rewrite path_sortedE // all_rev rev_sorted.
Qed.

Lemma sorted1 (r : rel A) xs : size xs == 1 -> sorted r xs.
Proof. by case: xs=>// x; case. Qed.

End Seq.

Section SeqEq.
Variable (A : eqType).

Lemma perm_cons2 (x y : A) s : perm_eq [:: x, y & s] [:: y, x & s].
Proof.
by rewrite (_ : [::x,y & s] = [::x] ++ [::y] ++ s) //
  (_ : [::y,x & s] = [::y] ++ [::x] ++ s) // perm_catCA.
Qed.

Lemma mem_split (x : A) s :
        x \in s -> exists s1 s2, s = s1 ++ [:: x] ++ s2.
Proof.
case/splitP=>s1 s2; exists s1, s2.
by rewrite -cats1 catA.
Qed.

Lemma mem_split_uniq (x : A) s :
       x \in s -> uniq s ->
         exists s1 s2, [/\ s = s1 ++ [:: x] ++ s2,
                           uniq (s1 ++ s2) &
                           x \notin s1 ++ s2].
Proof.
move=>/[swap] Hu /mem_split [s1 [s2 H]].
exists s1, s2; move: Hu.
by rewrite H uniq_catCA cons_uniq; case/andP.
Qed.

Lemma all_notin (p : pred A) xs y :
        all p xs -> ~~ p y -> y \notin xs.
Proof. by move/allP=>Ha; apply/contra/Ha. Qed.

Lemma subset_all a (s1 s2 : seq A) : {subset s1 <= s2} -> all a s2 -> all a s1.
Proof. by move=>Hs /allP Ha1; apply/allP=>s /Hs /Ha1. Qed.

End SeqEq.

Section Allrel.
Variables (S T : Type).

Lemma allrel_rconsl (r : T -> S -> bool) x xs ys :
        allrel r (rcons xs x) ys = allrel r xs ys && all (r x) ys.
Proof. by rewrite -cats1 allrel_catl allrel1l. Qed.

Lemma allrel_rconsr (r : T -> S -> bool) y xs ys :
        allrel r xs (rcons ys y) = allrel r xs ys && all (r^~ y) xs.
Proof. by rewrite -cats1 allrel_catr allrel1r. Qed.

End Allrel.

Section AllrelEq.
Variables (S T : eqType).

Lemma allrel_in_l (r : T -> S -> bool) (xs xs' : seq T) (ys : seq S) :
        xs =i xs' ->
        allrel r xs ys = allrel r xs' ys.
Proof.
by move=>H; rewrite !allrel_allpairsE; apply/eq_all_r/mem_allpairs_dep.
Qed.

Lemma allrel_in_r (r : T -> S -> bool) (xs : seq T) (ys ys' : seq S) :
        ys =i ys' ->
        allrel r xs ys = allrel r xs ys'.
Proof.
by move=>H; rewrite !allrel_allpairsE; apply/eq_all_r/mem_allpairs_dep.
Qed.

Lemma allrel_sub_l (r : T -> S -> bool) (xs xs' : seq T) (ys : seq S) :
        {subset xs' <= xs} ->
        allrel r xs ys -> allrel r xs' ys.
Proof.
move=>H Ha; apply/allrelP=>x y Hx Hy.
by move/allrelP: Ha; apply=>//; apply: H.
Qed.

Lemma allrel_sub_r (r : T -> S -> bool) (xs : seq T) (ys ys' : seq S) :
        {subset ys' <= ys} ->
        allrel r xs ys -> allrel r xs ys'.
Proof.
move=>H Ha; apply/allrelP=>x y Hx Hy.
by move/allrelP: Ha; apply=>//; apply: H.
Qed.

Lemma allrel_trans (xs ys : seq S) z r :
        transitive r ->
        all (r^~ z) xs -> all (r z) ys -> allrel r xs ys.
Proof.
move=>Ht /allP Ha /allP Hp; apply/allrelP=>x y + Hy.
by move/Ha/Ht; apply; apply: Hp.
Qed.

End AllrelEq.

Section SeqOrd.
Variable (A : ordType).

Lemma ord_neq (x y : A) : ord x y -> x != y.
Proof.
move=>H; apply/negP=>/eqP E.
by rewrite E irr in H.
Qed.

Lemma sorted_cat_cons_cat (l r : seq A) x :
        sorted ord (l ++ x :: r) = sorted ord (l ++ [::x]) && sorted ord (x::r).
Proof.
rewrite !(sorted_pairwise (@trans A)) cats1 pairwise_cat pairwise_rcons allrel_consr !pairwise_cons.
case/boolP: (all (ord^~ x) l)=>//= Hl; case/boolP: (all (ord x) r)=>/= [Hr|_]; last by rewrite !andbF.
by rewrite (allrel_trans (@trans A) Hl Hr).
Qed.

End SeqOrd.
