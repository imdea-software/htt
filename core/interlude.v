From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat seq eqtype path.
From fcsl Require Import options prelude ordtype.

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

Lemma allrel_rconsl (r : T -> S -> bool)
                    x xs ys : allrel r (rcons xs x) ys = allrel r xs ys && all (r x) ys.
Proof. by rewrite -cats1 allrel_catl allrel1l. Qed.

Lemma allrel_rconsr (r : T -> S -> bool)
                    y xs ys : allrel r xs (rcons ys y) = allrel r xs ys && all (r^~ y) xs.
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

Section FindLast.

Variables (T : Type).
Implicit Types (x : T) (p : pred T) (s : seq T).

(* find the last occurence in a single pass *)
Definition find_last_aux oi0 p s :=
  foldl (fun '(o,i) x => (if p x then Some i else o, i.+1)) oi0 s.

Lemma find_last_auxE oi0 p s :
  find_last_aux oi0 p s =
    let k := seq.find p (rev s) in
    (if k == size s then oi0.1 else Some (oi0.2 + (size s - k).-1), oi0.2 + size s).
Proof.
rewrite /find_last_aux; elim: s oi0=>/= [|x s IH] [o0 i0] /=; first by rewrite addn0.
rewrite IH /= rev_cons -cats1 find_cat /= has_find.
move: (find_size p (rev s)); rewrite size_rev; case: ltngtP=>// H _.
- case: eqP=>[E|_]; first by rewrite E ltnNge leqnSn in H.
  apply: injective_projections=>/=; [congr Some | rewrite addSnnS]=>//.
  by rewrite !predn_sub /= -predn_sub addSnnS prednK // subn_gt0.
case: ifP=>_; rewrite addSnnS; last by rewrite addn1 eqxx.
by rewrite addn0 eqn_leq leqnSn /= ltnn subSnn addn0.
Qed.

Definition find_last p s :=
  let '(o, i) := find_last_aux (None, 0) p s in odflt i o.

(* finding last is finding first in reversed list *)
Corollary find_lastE p s :
  find_last p s =
    let i := seq.find p (rev s) in
    if i == size s then size s else (size s - i).-1.
Proof. by rewrite /find_last find_last_auxE /= !add0n; case: ifP. Qed.

Lemma find_last_size p s : find_last p s <= size s.
Proof.
rewrite find_lastE /=; case: ifP=>// _.
by rewrite -subnS; apply: leq_subr.
Qed.

Lemma has_find_last p s : has p s = (find_last p s < size s).
Proof.
rewrite find_lastE /= -has_rev has_find -(size_rev s); case: ltngtP=>/=.
- move=>H; case/posnP: (size (rev s))=>[/eqP/nilP|] E.
  - by rewrite E /= in H.
  by rewrite -subnS ltn_subrL E.
- by rewrite ltnNge find_size.
by rewrite ltnn.
Qed.

Lemma hasNfind_last p s : ~~ has p s -> find_last p s = size s.
Proof. by rewrite has_find_last; case: ltngtP (find_last_size p s). Qed.

Lemma nth_find_last x0 p s : has p s -> p (nth x0 s (find_last p s)).
Proof.
rewrite find_lastE /= -has_rev -(size_rev s) => /[dup] E.
rewrite has_find ltn_neqAle; case/andP=>/negbTE H _; rewrite H.
move/(@nth_find _ x0): E; rewrite nth_rev; first by rewrite subnS size_rev.
by move: (find_size p (rev s)); rewrite leq_eqVlt H -(size_rev s).
Qed.

Lemma has_drop p s i : has p s -> has p (drop i.+1 s) = (i < find_last p s).
Proof.
rewrite find_lastE /= -has_rev -(size_rev s) => /[dup] E.
rewrite has_find =>/[dup] H.
rewrite ltn_neqAle; case/andP=>/negbTE -> _.
move/(has_take (size s - i).-1): E.
rewrite take_rev has_rev -subnS.
case/boolP: (i < size s)=>[Hi|].
- rewrite subKn // =>->; rewrite size_rev in H *.
  by rewrite ltn_subCr -[RHS]ltnS prednK // subn_gt0.
rewrite -ltnNge ltnS => Hi _.
rewrite drop_oversize /=; last by apply: (leq_trans Hi).
symmetry; apply/negbTE; rewrite size_rev -ltnNge ltnS.
by apply/leq_trans/Hi; rewrite -subnS; exact: leq_subr.
Qed.

Lemma find_gtn p s i : has p (drop i.+1 s) -> i < find_last p s.
Proof.
case/boolP: (has p s)=>Hp; first by rewrite (has_drop _ Hp).
suff: ~~ has p (drop i.+1 s) by move/negbTE=>->.
move: Hp; apply: contra; rewrite -{2}(cat_take_drop i.+1 s) has_cat=>->.
by rewrite orbT.
Qed.

Variant split_find_last_nth_spec p : seq T -> seq T -> seq T -> T -> Type :=
  FindLastNth x s1 s2 of p x & ~~ has p s2 :
    split_find_last_nth_spec p (rcons s1 x ++ s2) s1 s2 x.

Lemma split_find_last_nth x0 p s (i := find_last p s) :
  has p s -> split_find_last_nth_spec p s (take i s) (drop i.+1 s) (nth x0 s i).
Proof.
move=> p_s; rewrite -[X in split_find_last_nth_spec _ X](cat_take_drop i s).
rewrite (drop_nth x0 _); last by rewrite -has_find_last.
rewrite -cat_rcons; constructor; first by apply: nth_find_last.
by rewrite has_drop // ltnn.
Qed.

Variant split_find_last_spec p : seq T -> seq T -> seq T -> Type :=
  FindLastSplit x s1 s2 of p x & ~~ has p s2 :
    split_find_last_spec p (rcons s1 x ++ s2) s1 s2.

Lemma split_find_last p s (i := find_last p s) :
  has p s -> split_find_last_spec p s (take i s) (drop i.+1 s).
Proof.
by case: s => // x ? in i * => ?; case: split_find_last_nth => //; constructor.
Qed.

End FindLast.

Section FindLastEq.

Variables (T : eqType).
Implicit Type p : seq T.

Definition index_last (x : T) := find_last (pred1 x).

Lemma memNindex_last x s : x \notin s -> index_last x s = size s.
Proof. by rewrite -has_pred1=>/hasNfind_last. Qed.

Lemma index_last_cons x y t : index_last x (y::t) =
  if x \in t then (index_last x t).+1 else if y == x then 0 else (size t).+1.
Proof.
rewrite /index_last !find_lastE /= rev_cons -cats1 find_cat /= has_rev has_pred1.
case/boolP: (x \in t)=>H; last first.
- rewrite size_rev; case/boolP: (y == x)=>/= _; last by rewrite addn1 eqxx.
  by rewrite addn0 eqn_leq leqnSn /= ltnn subSnn.
rewrite -mem_rev -has_pred1 has_find in H; rewrite -(size_rev t).
case: ltngtP H=>//= H _.
case: ifP=>[/eqP E|_]; first by rewrite E ltnNge leqnSn in H.
by rewrite predn_sub /= prednK // subn_gt0.
Qed.

Lemma index_gtn x s i : x \in drop i.+1 s -> i < index_last x s.
Proof. by rewrite -has_pred1; apply: find_gtn. Qed.

Lemma index_last_uniq x s : uniq s -> index_last x s = index x s.
Proof.
move=>H; case/boolP: (x \in s)=>Hx; last first.
- by rewrite (memNindex_last Hx) (memNindex Hx).
elim: s x H Hx=>//= h t IH x.
rewrite index_last_cons.
case/andP=>Hh Ht; rewrite inE eq_sym; case/orP.
- by move/eqP=>{x}<-; rewrite (negbTE Hh) eqxx.
move=>Hx; rewrite Hx; case: eqP=>[E|_]; last by congr S; apply: IH.
by rewrite E Hx in Hh.
Qed.

Variant splitLast x : seq T -> seq T -> seq T -> Type :=
  SplitLast p1 p2 of x \notin p2 : splitLast x (rcons p1 x ++ p2) p1 p2.

Lemma splitLastP s x (i := index_last x s) :
  x \in s -> splitLast x s (take i s) (drop i.+1 s).
Proof.
case: s => // y s in i * => H.
case: split_find_last_nth=>//; first by rewrite has_pred1.
move=>_ s1 s2 /= /eqP->; rewrite has_pred1 => H2.
by constructor.
Qed.

End FindLastEq.
