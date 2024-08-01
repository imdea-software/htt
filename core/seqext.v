(*
Copyright 2013 IMDEA Software Institute
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*)

From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat seq path eqtype choice fintype bigop.
From pcm Require Import options prelude pred.

(*********************)
(* Extensions to seq *)
(*********************)

Lemma nilp_hasPn {A} (s : seq A) : nilp s = ~~ has predT s.
Proof. by case: s. Qed.

Lemma filter_predIC {A} (s : seq A) p1 p2 :
         filter (predI p1 p2) s = filter (predI p2 p1) s.
Proof. by apply: eq_filter => z /=; rewrite andbC. Qed.

Lemma filter_swap {A} (s : seq A) p1 p2 :
        filter p1 (filter p2 s) = filter p2 (filter p1 s).
Proof. by rewrite -!filter_predI filter_predIC. Qed.

(* TODO contribute to mathcomp? *)
Lemma map_nilp {A B} (f : A -> B) (s : seq A) : nilp (map f s) = nilp s.
Proof. by rewrite /nilp; case: s. Qed.

Lemma filter_nilp {A} (p : pred A) (s : seq A) : nilp (filter p s) = ~~ has p s.
Proof. by rewrite /nilp size_filter -leqn0 leqNgt has_count. Qed.

Lemma head_map {P Q} (f : P -> Q) z (s : seq P) :
        f (head z s) = head (f z) (map f s).
Proof. by case: s. Qed.

Lemma zip_map2 {P Q R S} (f : P -> R) (g : Q -> S) (s1 : seq P) (s2 : seq Q) :
        zip (map f s1) (map g s2) =
        map (fun '(x1,x2) => (f x1,g x2)) (zip s1 s2).
Proof.
elim: s1 s2=>/= [|x1 s1 IH] [|x2 s2] //=.
by congr cons.
Qed.

Corollary zip_mapl {P Q R} (f : P -> R) (s1 : seq P) (s2 : seq Q) :
            zip (map f s1) s2 =
            map (fun '(x1,x2) => (f x1,x2)) (zip s1 s2).
Proof. by rewrite -{1}(map_id s2) zip_map2. Qed.

Corollary zip_mapr {P Q S} (g : Q -> S) (s1 : seq P) (s2 : seq Q) :
            zip s1 (map g s2) =
            map (fun '(x1,x2) => (x1,g x2)) (zip s1 s2).
Proof. by rewrite -{1}(map_id s1) zip_map2. Qed.

Lemma drop_take_id {A} x (s : seq A) : drop x (take x s) = [::].
Proof. by rewrite -{2}(add0n x) -take_drop take0. Qed.

Lemma drop_take_mask {A} (s : seq A) x y :
        drop x (take y s) = mask (nseq x false ++ nseq (y-x) true) s.
Proof.
case: (ltnP x (size s))=>Hx; last first.
- rewrite drop_oversize; last by rewrite size_take_min geq_min Hx orbT.
  rewrite -{1}(subnKC Hx) nseqD -catA -{3}(cats0 s) mask_cat; last by rewrite size_nseq.
  by rewrite mask0 mask_false.
have Hx': size (nseq x false) = size (take x s).
- by rewrite size_nseq size_take_min; symmetry; apply/minn_idPl/ltnW.
rewrite -{2}(cat_take_drop x s) mask_cat // mask_false /= -takeEmask take_drop.
case: (leqP x y)=>[Hxy|/ltnW Hxy]; first by rewrite subnK.
move: (Hxy); rewrite -subn_eq0=>/eqP->; rewrite add0n drop_take_id.
by rewrite drop_oversize // size_take_min geq_min Hxy.
Qed.

Section LemmasEq.
Variables (A : eqType).
Implicit Type xs : seq A.

(* With A : Type, we have the In_split lemma. *)
(* With A : eqType, the lemma can be strenghtened to *)
(* not only return the split of xs, but the split of xs *)
(* that uses the first occurrence of x is xs *)
Lemma in_split xs x :
        x \in xs -> exists xs1 xs2, xs = xs1 ++ x :: xs2 /\ x \notin xs1.
Proof.
rewrite -has_pred1; case/split_find=>_ s1 s2 /eqP ->.
by rewrite has_pred1=>H; exists s1, s2; rewrite -cats1 -catA.
Qed.

Lemma subset_nilR xs :
        {subset xs <= [::]} -> xs = [::].
Proof. by case: xs=>// x xs /(_ x); rewrite inE eqxx=>/(_ erefl). Qed.

Lemma subset_nil xs ys :
        {subset xs <= ys} -> ys = [::] -> xs = [::].
Proof. by move=>X E; move: E X=>->; apply: subset_nilR. Qed.

Lemma all_mem xs ys :
        reflect {subset ys <= xs} (all [mem xs] ys).
Proof. by case: allP=>H; constructor; [move=>x /H | move=>X; apply: H=>x /X]. Qed.

Lemma all_predC_sym xs ys :
        all [predC xs] ys = all [predC ys] xs.
Proof. by rewrite all_predC has_sym -all_predC. Qed.

Lemma nilp_filter (p : pred A) s :
        reflect {in s, forall z, ~~ p z} (nilp (filter p s)).
Proof.
case E : (nilp _); constructor.
- move: E; rewrite nilp_hasPn=>/hasPn H x Kx; apply/negP=>Px.
  by move: (H x); rewrite mem_filter Px=>/(_ Kx).
move=>X; move/negP: E; elim.
rewrite nilp_hasPn; apply/negP=>/hasP [x].
rewrite mem_filter=>/andP [Px Kx] _.
by move: (X x Kx); rewrite Px.
Qed.

Lemma index_rcons a x xs :
        index a (rcons xs x) =
        if a \in xs then index a xs else
          if a == x then size xs else (size xs).+1.
Proof.
rewrite eq_sym; elim: xs=>[|y xs IH] //=.
rewrite inE eq_sym; case: eqP=>//= _.
by rewrite IH; case: ifP=>// _; case: eqP.
Qed.

Lemma index_memN x xs :
        x \notin xs <-> index x xs = size xs.
Proof.
split; first by exact: memNindex.
by move=>E; rewrite -index_mem E ltnn.
Qed.

Corollary index_sizeE x xs :
            reflect (index x xs = size xs) (x \notin xs).
Proof. by apply/(equivP idP)/index_memN. Qed.

Lemma size0nilP xs :
        reflect (xs = [::]) (size xs == 0).
Proof.
case: eqP=>X; constructor; first by move/size0nil: X.
by move=>N; rewrite N in X.
Qed.

Lemma has_nilP xs :
        reflect (has predT xs) (xs != [::]).
Proof. by case: xs=>[|x xs]; constructor. Qed.

Lemma map_nilP {B : eqType} (f : B -> A) s :
        reflect (exists k, k \in map f s) (map f s != [::]).
Proof.
case: has_nilP=>X; constructor.
- by case/hasP: X=>x; exists x.
by case=>k K; elim: X; apply/hasP; exists k.
Qed.

Lemma filter_nilP (p : pred A) xs :
        reflect (forall x, p x -> x \in xs -> false)
                ([seq x <- xs | p x] == [::]).
Proof.
case: eqP=>E; constructor.
- move=>x H1 H2; suff : x \in [seq x <- xs | p x] by rewrite E.
  by rewrite mem_filter H1 H2.
move=>H; apply: E; apply: size0nil; apply/eqP; rewrite size_filter.
by rewrite eqn0Ngt -has_count; apply/hasPn=>x /H; case: (p x)=>//; apply.
Qed.

Lemma filter_pred1 x xs :
        x \notin xs -> filter (pred1 x) xs = [::].
Proof.
move=>H; apply/eqP; apply/filter_nilP=>z /eqP ->.
by rewrite (negbTE H).
Qed.

Lemma filter_predC1 x xs :
        x \notin xs -> filter (predC1 x) xs = xs.
Proof.
by move=>H; apply/all_filterP/allP=>y /=; case: eqP=>// ->; apply/contraL.
Qed.

Lemma filter_mem_sym (s1 s2 : seq A) :
        filter (mem s1) s2 =i filter (mem s2) s1.
Proof. by move=>x; rewrite !mem_filter andbC. Qed.

Lemma index_inj xs x y :
        x \in xs -> index x xs = index y xs -> x = y.
Proof.
elim: xs=>[|k xs IH] //=; rewrite inE eq_sym.
case: eqP=>[->{k} _|_ /= S]; case: eqP=>// _ []; apply: IH S.
Qed.

Lemma cat_cancel (xs1 xs2 ys1 ys2 : seq A) (k : A) :
        k \notin xs1 -> k \notin xs2 ->
        xs1 ++ k :: ys1 = xs2 ++ k :: ys2 ->
        (xs1 = xs2) * (ys1 = ys2).
Proof.
move=>Nk1 Nk2 E.
have Es : size xs1 = size xs2.
- have : index k (xs1++k::ys1) = index k (xs2++k::ys2) by rewrite E.
  by rewrite !index_cat /= (negbTE Nk1) (negbTE Nk2) eqxx !addn0.
have Ex : xs1 = take (size xs1) (xs1 ++ k :: ys1).
- by rewrite take_cat ltnn subnn /= cats0.
rewrite E Es take_cat ltnn subnn /= cats0 in Ex.
rewrite {xs1 Nk1 Es}Ex in E *.
have : ys1 = drop (size (xs2++[::k])) (xs2++k::ys1).
- by rewrite drop_cat size_cat /= addn1 ltnNge ltnW //= subSn // subnn /= drop0.
by rewrite E drop_cat size_cat /= addn1 ltnNge ltnW //= subSn // subnn /= drop0.
Qed.

(* if the list is not empty, the default value in head doesn't matter *)
Lemma head_dflt (x1 x2 x : A) xs :
        x \in xs -> head x1 xs = head x2 xs.
Proof. by case: xs. Qed.

Lemma mem_head (x : A) xs : head x xs \in x :: xs.
Proof. by case: xs=>[|y ys]; rewrite !inE //= eqxx orbT. Qed.

(* a common pattern of using mem_head that avoids forward reasoning *)
Lemma mem_headI (x : A) xs a :
        a = head x xs -> a \in x :: xs.
Proof. by move=>->; apply: mem_head. Qed.

Lemma head_nilp (x : A) xs :
        x \notin xs -> head x xs = x -> nilp xs.
Proof.
elim: xs=>[|y ys IH] //= H1 H2.
by rewrite H2 inE eqxx /= in H1.
Qed.

Lemma head_notin (x y : A) xs :
        y \in xs -> x \notin xs -> head x xs != x.
Proof.
move=>Y X; apply/negP=>/eqP; move/(head_nilp X)/nilP=>E.
by rewrite E in Y.
Qed.

(* weaker form of in_mask *)
(* TODO contribute to mathcomp *)
Lemma in_mask_count x m xs :
        count_mem x xs <= 1 ->
        x \in mask m xs = (x \in xs) && nth false m (index x xs).
Proof.
elim: xs m => [|y xs IHs] m /=; first by rewrite mask0 in_nil.
case: m=>/=[|b m]; first by rewrite in_nil nth_nil andbF.
case: b; rewrite !inE eq_sym; case: eqP=>//= _.
- by rewrite add0n; apply: IHs.
- rewrite -{2}(addn0 1%N) leq_add2l leqn0 => /eqP Hc.
  rewrite IHs; last by rewrite Hc.
  by move/count_memPn/negbTE: Hc=>->.
by rewrite add0n; apply: IHs.
Qed.

Lemma mem_take_index x xs :
        x \notin take (index x xs) xs.
Proof.
elim: xs=>//=h xs; case: eqP=>//= /eqP H IH.
by rewrite inE negb_or eq_sym H.
Qed.

Lemma prefix_drop_sub (s1 s2 : seq A) :
        seq.prefix s1 s2 ->
        forall n, {subset (drop n s1) <= drop n s2}.
Proof.
case/seq.prefixP=>s0 {s2}-> n x H.
rewrite drop_cat; case: ltnP=>Hn.
- by rewrite mem_cat H.
by move: H; rewrite drop_oversize.
Qed.

End LemmasEq.

(* finding last occurrence *)

Section FindLast.
Variables (T : Type).
Implicit Types (x : T) (p : pred T) (s : seq T).

(* helper function for finding the last occurrence in a single pass *)
(* calculates index and size *)
Definition findlast_aux oi0 p s : option nat * nat :=
  foldl (fun '(o,i) x => (if p x then Some i else o, i.+1)) oi0 s.

Lemma findlast_auxE oi0 p s :
        findlast_aux oi0 p s =
        let k := seq.find p (rev s) in
        (if k == size s then oi0.1
           else Some (oi0.2 + (size s - k).-1), oi0.2 + size s).
Proof.
rewrite /findlast_aux; elim: s oi0=>/= [|x s IH] [o0 i0] /=; first by rewrite addn0.
rewrite IH /= rev_cons -cats1 find_cat /= has_find.
move: (find_size p (rev s)); rewrite size_rev; case: ltngtP=>// H _.
- case: eqP=>[E|_]; first by rewrite E ltnNge leqnSn in H.
  apply: injective_projections=>/=; [congr Some | rewrite addSnnS]=>//.
  by rewrite !predn_sub /= -predn_sub addSnnS prednK // subn_gt0.
case: ifP=>_; rewrite addSnnS; last by rewrite addn1 eqxx.
by rewrite addn0 eqn_leq leqnSn /= ltnn subSnn addn0.
Qed.

Definition findlast p s : nat :=
  let '(o, i) := findlast_aux (None, 0) p s in odflt i o.

(* finding last is finding first in reversed list and flipping indices *)
Corollary findlastE p s :
            findlast p s =
            if has p s then (size s - seq.find p (rev s)).-1
                       else size s.
Proof.
rewrite /findlast findlast_auxE /= !add0n -has_rev; case/boolP: (has p (rev s)).
- by rewrite has_find size_rev; case: ltngtP.
by move/hasNfind=>->; rewrite size_rev eqxx.
Qed.

Lemma findlast_size p s : findlast p s <= size s.
Proof.
rewrite findlastE; case: ifP=>// _.
by rewrite -subnS; apply: leq_subr.
Qed.

Lemma has_findlast p s : has p s = (findlast p s < size s).
Proof.
symmetry; rewrite findlastE; case: ifP=>H /=; last by rewrite ltnn.
by rewrite -subnS /= ltn_subrL /=; case: s H.
Qed.

Lemma hasNfindlast p s : ~~ has p s -> findlast p s = size s.
Proof. by rewrite has_findlast; case: ltngtP (findlast_size p s). Qed.

Lemma findlast0 p x : findlast p [::] = 0.
Proof. by []. Qed.

Lemma findlast1 p x : findlast p [::x] = ~~ p x.
Proof. by rewrite findlastE /= orbF; case: ifP=>// ->. Qed.

Lemma findlast_cat p s1 s2 :
        findlast p (s1 ++ s2) =
        if has p s1 && ~~ has p s2
          then findlast p s1
          else size s1 + findlast p s2.
Proof.
rewrite !findlastE has_cat rev_cat find_cat has_rev size_cat size_rev.
case/boolP: (has p s2)=>H2; last first.
- rewrite orbF; case/boolP: (has p s1)=>//= H1.
  by rewrite addnC subnDl.
have H2' : find p (rev s2) < size s2.
- by rewrite -size_rev -has_find has_rev.
rewrite /= orbT andbF -addnBA; last by apply: ltnW.
rewrite -!subn1 -subnDA -addnBA; last by rewrite subn_gt0.
by rewrite subnDA.
Qed.

Lemma findlast_cons p x s :
        findlast p (x::s) =
        if p x && ~~ has p s then 0 else (findlast p s).+1.
Proof.
rewrite -cat1s findlast_cat /= !add1n orbF findlast1.
by case: ifP=>// /andP [->].
Qed.

Lemma findlast_rcons p x s :
        findlast p (rcons s x) =
        if p x then size s
          else if has p s then findlast p s
                          else (size s).+1.
Proof.
rewrite -cats1 findlast_cat /= orbF findlast1.
case: (p x)=>/=; first by rewrite andbF addn0.
by rewrite andbT addn1.
Qed.

Lemma nth_findlast x0 p s : has p s -> p (nth x0 s (findlast p s)).
Proof.
rewrite findlastE=>/[dup] E ->; rewrite -has_rev in E.
rewrite -subnS -nth_rev; last by rewrite -size_rev -has_find.
by apply: nth_find.
Qed.

Lemma has_drop p s i : has p s -> has p (drop i s) = (i <= findlast p s).
Proof.
rewrite findlastE=>/[dup] E ->; rewrite -has_rev in E.
have Hh: 0 < size s - find p (rev s).
- by rewrite -size_rev subn_gt0 -has_find.
rewrite -size_rev; move/(has_take (size s - i)): (E).
rewrite take_rev -subnS size_rev.
case/boolP: (i < size s)=>[Hi|].
- rewrite subnA //; last by apply: ltnW.
  rewrite subnn add0n has_rev=>->.
  rewrite ltn_subRL addnC -ltn_subRL subnS.
  by case: (size s - find p (rev s)) Hh.
rewrite -ltnNge ltnS => Hi _.
rewrite drop_oversize //=; symmetry; apply/negbTE.
rewrite -ltnNge subnS prednK //.
by apply/leq_trans/Hi; exact: leq_subr.
Qed.

Lemma find_geq p s i : has p (drop i s) -> i <= findlast p s.
Proof.
case/boolP: (has p s)=>Hp; first by rewrite (has_drop _ Hp).
suff: ~~ has p (drop i s) by move/negbTE=>->.
move: Hp; apply: contra; rewrite -{2}(cat_take_drop i s) has_cat=>->.
by rewrite orbT.
Qed.

Lemma find_leq_last p s : find p s <= findlast p s.
Proof.
rewrite findlastE.
case/boolP: (has p s)=>[|_]; last by apply: find_size.
elim: s=>//= h s IH.
rewrite rev_cons -cats1 find_cat has_rev size_rev /=.
case/orP; first by move=>->.
move=>/[dup] H ->; case: ifP=>_ //.
rewrite subSn /=; last first.
- by rewrite -size_rev; apply: find_size.
apply: (leq_ltn_trans (IH H)); rewrite ltn_predL subn_gt0.
by rewrite -size_rev -has_find has_rev.
Qed.

Variant split_findlast_nth_spec p : seq T -> seq T -> seq T -> T -> Type :=
  FindLastNth x s1 s2 of p x & ~~ has p s2 :
    split_findlast_nth_spec p (rcons s1 x ++ s2) s1 s2 x.

Lemma split_findlast_nth x0 p s (i := findlast p s) :
        has p s ->
        split_findlast_nth_spec p s (take i s) (drop i.+1 s) (nth x0 s i).
Proof.
move=> p_s; rewrite -[X in split_findlast_nth_spec _ X](cat_take_drop i s).
rewrite (drop_nth x0 _); last by rewrite -has_findlast.
rewrite -cat_rcons; constructor; first by apply: nth_findlast.
by rewrite has_drop // ltnn.
Qed.

Variant split_findlast_spec p : seq T -> seq T -> seq T -> Type :=
  FindLastSplit x s1 s2 of p x & ~~ has p s2 :
    split_findlast_spec p (rcons s1 x ++ s2) s1 s2.

Lemma split_findlast p s (i := findlast p s) :
        has p s ->
        split_findlast_spec p s (take i s) (drop i.+1 s).
Proof.
by case: s => // x ? in i * =>?; case: split_findlast_nth=>//; constructor.
Qed.

End FindLast.

Section FindLastEq.
Variables (T : eqType).
Implicit Type s : seq T.

Definition indexlast (x : T) : seq T -> nat := findlast (pred1 x).

Lemma indexlast_size x s : indexlast x s <= size s.
Proof. by rewrite /indexlast; apply: findlast_size. Qed.

Lemma indexlast_mem x s : (indexlast x s < size s) = (x \in s).
Proof. by rewrite /indexlast -has_findlast has_pred1. Qed.

Lemma memNindexlast x s : x \notin s -> indexlast x s = size s.
Proof. by rewrite -has_pred1=>/hasNfindlast. Qed.

Lemma indexlast0 x : indexlast x [::] = 0.
Proof. by []. Qed.

Lemma indexlast1 x y : indexlast x [::y] = (x != y).
Proof. by rewrite /indexlast findlast1 /= eq_sym. Qed.

Lemma indexlast_cat x s1 s2 :
        indexlast x (s1 ++ s2) =
        if (x \in s1) && (x \notin s2)
          then indexlast x s1
          else size s1 + indexlast x s2.
Proof. by rewrite /indexlast findlast_cat !has_pred1. Qed.

Lemma indexlast_cons x y s :
        indexlast x (y::s) =
        if (y == x) && (x \notin s) then 0 else (indexlast x s).+1.
Proof. by rewrite /indexlast findlast_cons has_pred1. Qed.

Lemma indexlast_rcons x y s :
        indexlast x (rcons s y) =
        if y == x then size s
          else if x \in s then indexlast x s
                          else (size s).+1.
Proof. by rewrite /indexlast findlast_rcons has_pred1. Qed.

Lemma index_geq x s i : x \in drop i s -> i <= indexlast x s.
Proof. by rewrite -has_pred1; apply: find_geq. Qed.

Lemma index_leq_last x s : index x s <= indexlast x s.
Proof. by apply: find_leq_last. Qed.

Lemma indexlast_count x s : count_mem x s <= 1 <-> index x s = indexlast x s.
Proof.
elim: s=>//= h t IH; rewrite indexlast_cons.
case: eqP=>/= ?; last first.
- by rewrite add0n IH; split=>[->|[]].
rewrite add1n ltnS leqn0; split.
- by move/eqP/count_memPn=>->.
by case: ifP=>//= /count_memPn->.
Qed.

Corollary index_lt_last x s : 1 < count_mem x s -> index x s < indexlast x s.
Proof.
move=>H; move: (index_leq_last x s); rewrite leq_eqVlt.
by case: eqP=>//= /indexlast_count; case: leqP H.
Qed.

Corollary indexlast_uniq x s : uniq s -> index x s = indexlast x s.
Proof.
move=>H; apply/indexlast_count.
by rewrite count_uniq_mem //; apply: leq_b1.
Qed.

Lemma indexlast_memN x xs :
        x \notin xs <-> indexlast x xs = size xs.
Proof.
split; first by exact: memNindexlast.
by move=>E; rewrite -indexlast_mem E ltnn.
Qed.

Lemma index_last_inj x y s :
        (x \in s) || (y \in s) -> index x s = indexlast y s -> x = y.
Proof.
elim: s=>[|k s IH] //=; rewrite !inE indexlast_cons !(eq_sym k).
case: eqP=>[{k}<- _|_ /= S]; first by case: eqP=>//=.
move: S; case/boolP: (y \in s)=>/=.
- by rewrite andbF=>H _ []; apply: IH; rewrite H orbT.
move=>Ny; rewrite orbF andbT.
by case: eqP=>//; rewrite orbF=>_ H []; apply: IH; rewrite H.
Qed.

Lemma indexlast_inj x y s :
        x \in s -> indexlast x s = indexlast y s -> x = y.
Proof.
elim: s=>[|k s IH] //=; rewrite inE eq_sym !indexlast_cons.
case: eqP=>[->{k} _|_ /= S] /=.
- case: eqP=>//= _.
  by case: ifP=>// /negbT; rewrite negbK=>H; case; apply: IH.
by case: ifP=>// _ []; apply: IH.
Qed.

Lemma mem_drop_indexlast x s :
        x \notin drop (indexlast x s).+1 s.
Proof.
elim: s=>//=h s; rewrite indexlast_cons.
case: eqP=>//= _ H.
by case: ifP=>//=; rewrite drop0.
Qed.

Variant splitLast x : seq T -> seq T -> seq T -> Type :=
  SplitLast p1 p2 of x \notin p2 : splitLast x (rcons p1 x ++ p2) p1 p2.

Lemma splitLastP s x (i := indexlast x s) :
        x \in s ->
        splitLast x s (take i s) (drop i.+1 s).
Proof.
case: s => // y s in i * => H.
case: split_findlast_nth=>//; first by rewrite has_pred1.
move=>_ s1 s2 /= /eqP->; rewrite has_pred1 => H2.
by constructor.
Qed.

End FindLastEq.

(* finding all occurrences *)

Section FindAll.

Variables (T : Type).
Implicit Types (x : T) (p : pred T) (s : seq T).

(* helper function for finding all occurrences in a single pass with difference lists *)
Definition findall_aux oi0 p s : (seq nat -> seq nat) * nat :=
  foldl (fun '(s,i) x => (if p x then s \o cons i else s, i.+1)) oi0 s.

Lemma findall_auxE oi0 p s :
      (forall s1 s2 : seq nat, oi0.1 (s1 ++ s2) = oi0.1 s1 ++ s2) ->
      let: (rs, ix) := findall_aux oi0 p s in
        (forall s' : seq nat,
           rs s' = oi0.1 (unzip1 (filter (p \o snd) (zip (iota oi0.2 (size s)) s))) ++ s')
        /\ ix = oi0.2 + size s.
Proof.
move; rewrite /findall_aux; elim: s oi0=>[|x s IH] [o0 i0] /= H0.
- split; last by rewrite addn0.
  by move=>s'; rewrite -{1}(cat0s s') H0.
case/boolP: (p x)=>/= Hpx.
- move: (IH (o0 \o cons i0, i0.+1))=>/=.
  rewrite addSn addnS; apply=>s1 s2.
  by rewrite -cat_cons H0.
by move: (IH (o0, i0.+1))=>/=; rewrite addSn addnS; apply.
Qed.

Definition findall p s : seq nat := (findall_aux (id, 0) p s).1 [::].

Lemma findallE p s :
        findall p s = unzip1 (filter (p \o snd) (zip (iota 0 (size s)) s)).
Proof.
rewrite /findall.
move: (@findall_auxE (id, 0) p s)=>/= /(_ (fun s1 s2 : seq nat => erefl)).
case E: (findall_aux (id, 0) p s)=>[rs ix] /=; case=>/(_ [::]) -> _.
by rewrite cats0.
Qed.

Lemma findall_cat p s1 s2 :
        findall p (s1 ++ s2) =
        findall p s1 ++ map (fun n => size s1 + n) (findall p s2).
Proof.
rewrite !findallE size_cat iotaD add0n zip_cat; last by rewrite size_iota.
rewrite filter_cat {1}/unzip1 map_cat; congr (_ ++ _).
set n := size s1.
rewrite -{1}(addn0 n) iotaDl zip_mapl filter_map -!map_comp.
rewrite (eq_filter (a2:=(p \o snd))); last by case.
by apply: eq_map; case.
Qed.

Corollary findall_cons p x s :
            findall p (x::s) =
            if p x then 0 :: map S (findall p s) else map S (findall p s).
Proof. by rewrite -cat1s findall_cat /= findallE /=; case: (p x). Qed.

Corollary findall_rcons p x s :
            findall p (rcons s x) =
            if p x then rcons (findall p s) (size s) else findall p s.
Proof.
rewrite -cats1 findall_cat /= !findallE /=; case: (p x)=>/=.
- by rewrite addn0 cats1.
by rewrite cats0.
Qed.

Lemma findall_size p s :
        size (findall p s) = count p s.
Proof.
by elim: s=>//=x s IH; rewrite findall_cons; case: (p x)=>/=;
rewrite size_map IH.
Qed.

Lemma findall_nilp p s :
        nilp (findall p s) = ~~ has p s.
Proof. by rewrite /nilp findall_size has_count -leqNgt leqn0. Qed.

Lemma findall_head p s :
        find p s = head (size s) (findall p s).
Proof.
elim: s=>//=x s IH; rewrite findall_cons; case: (p x)=>//=.
by rewrite -head_map IH.
Qed.

Lemma findall_last p s :
        findlast p s = last (size s) (findall p s).
Proof.
elim/last_ind: s=>//=s x IH; rewrite findall_rcons findlast_rcons size_rcons.
case: (p x)=>/=; first by rewrite last_rcons.
by rewrite IH -(negbK (has _ _)) -findall_nilp; case: (findall p s).
Qed.

Lemma findall_count1 p s :
        count p s <= 1 ->
        findall p s = if has p s then [::find p s] else [::].
Proof.
rewrite -(findall_size p s); case E: (findall p s)=>[|h t] /=.
- by move/nilP: E; rewrite findall_nilp=>/negbTE ->.
have ->: has p s by rewrite -(negbK (has p s)) -findall_nilp E.
rewrite ltnS leqn0 => /eqP/size0nil Et; move: E; rewrite {t}Et.
by rewrite findall_head=>->.
Qed.

End FindAll.

Section FindAllEq.

Variables (T : eqType).
Implicit Type s : seq T.

Definition indexall (x : T) : seq T -> seq nat := findall (pred1 x).

Lemma indexall_size x s :
        size (indexall x s) = count_mem x s.
Proof. by rewrite /indexall findall_size. Qed.

Lemma indexall_mem x s : nilp (indexall x s) = (x \notin s).
Proof. by rewrite /indexall findall_nilp has_pred1. Qed.

Lemma indexall_head x s :
        index x s = head (size s) (indexall x s).
Proof. by rewrite /index /indexall findall_head. Qed.

Lemma indexall_last x s :
        indexlast x s = last (size s) (indexall x s).
Proof. by rewrite /indexlast /indexall findall_last. Qed.

Lemma indexall_count1 x s :
        count_mem x s <= 1 ->
        indexall x s = if x \in s then [::index x s] else [::].
Proof. by rewrite /indexall /index -has_pred1; apply: findall_count1. Qed.

Corollary indexall_uniq x s :
            uniq s ->
            indexall x s = if x \in s then [::index x s] else [::].
Proof. by move=>U; apply: indexall_count1; rewrite (count_uniq_mem _ U) leq_b1. Qed.

End FindAllEq.

(* Interaction of filter/last/index *)

Section FilterLastIndex.
Variables (A : eqType).

(* if s has an element, last returns one of them *)
Lemma last_in x k (s : seq A) : x \in s -> last k s \in s.
Proof.
elim: s k=>[|k s IH] k' //=; rewrite !inE.
case/orP=>[/eqP <-|/IH ->]; first by apply: mem_last.
by rewrite orbT.
Qed.

Arguments last_in x [k s].

Lemma last_notin x k (s : seq A) : x \in s -> k \notin s -> last k s != k.
Proof. by move/(last_in _ (k:=k))=>H /negbTE; case: eqP H=>// ->->. Qed.

Lemma last_notin_nilp k (s : seq A) : ~~ nilp s -> k \notin s -> last k s != k.
Proof.
move=>N; apply: (last_notin (x := head k s)).
by case: s N=>//= x s _; rewrite inE eqxx.
Qed.

(* last either returns a default, or one of s's elements *)
Lemma last_change k (s : seq A) : last k s != k -> last k s \in s.
Proof. by move: (mem_last k s); rewrite inE; case: eqP. Qed.

Lemma last_changeE1 k (s : seq A) :
        last k s != k -> forall x, last x s = last k s.
Proof. by elim: s k=>[|k s IH] y //=; rewrite eqxx. Qed.

Lemma last_changeE2 k (s : seq A) :
        last k s != k -> forall x, x \notin s -> last x s != x.
Proof. by move/last_change/last_notin. Qed.

(* common formats of last_change *)
Lemma last_nochange k (s : seq A) : last k s = k -> (k \in s) || (s == [::]).
Proof.
case: s k=>[|k s] //= k'; rewrite inE; case: eqP=>[->|N L] //.
by move: (@last_change k s); rewrite L=>-> //; case: eqP N.
Qed.

Lemma last_nochange_nil k (s : seq A) : last k s = k -> k \notin s -> s = [::].
Proof. by move/last_nochange; case/orP=>[/negbF ->|/eqP]. Qed.

(* last and rcons *)

Lemma rcons_lastX x y (s : seq A) :
        x \in s -> exists s', s = rcons s' (last y s).
Proof.
elim/last_ind: s=>[|ks k IH] //=.
by rewrite last_rcons; exists ks.
Qed.

Lemma rcons_lastP x (s : seq A) :
        reflect (exists s', s = rcons s' (last x s)) (last x s \in s).
Proof.
case X : (last x s \in s); constructor; first by apply: rcons_lastX X.
case=>s' E; move/negP: X; elim.
by rewrite E last_rcons mem_rcons inE eqxx.
Qed.

Lemma rcons_lastXP x y (s : seq A) :
        reflect (exists s', s = rcons s' x) ((x == last y s) && (x \in s)).
Proof.
case: eqP=>[->|N]; first by apply: rcons_lastP.
by constructor; case=>s' E; elim: N; rewrite E last_rcons.
Qed.

Lemma index_last_size_uniq z (s : seq A) :
        uniq s ->
        index (last z s) s = (size s).-1.
Proof.
elim: s z=>//= x s IH z.
case/andP=>Nx U; rewrite eq_sym; case: eqVneq=>H.
- by rewrite (last_nochange_nil H Nx).
rewrite {}IH //; apply: prednK.
by case: {Nx U}s H=>//=; rewrite eqxx.
Qed.

(* last has bigger index than anything in x *)
Lemma index_last_mono x k (s : seq A) :
         uniq s -> x \in s -> index x s <= index (last k s) s.
Proof.
elim: s k=>[|k s IH] //= k'; rewrite inE !(eq_sym k).
case/andP=>K U; case: (x =P k)=>//= /eqP N X.
case: (last k s =P k)=>[/last_nochange|/eqP L].
- by case: eqP X=>[->//|]; rewrite (negbTE K).
by apply: leq_trans (IH k U X) _.
Qed.

(* if it has bigger index, and is in the list, then it's last *)
Lemma max_index_last (s : seq A) (x y : A) :
         uniq s -> x \in s ->
         (forall z, z \in s -> index z s <= index x s) -> last y s = x.
Proof.
elim: s y=>[|k s IH] y //= /andP [Nk U]; rewrite inE (eq_sym k).
case: (x =P k) Nk=>[<-{k} Nk _|_ Nk /= S] /= D; last first.
- apply: IH=>// z Z; move: (D z); rewrite inE Z orbT=>/(_ (erefl _)).
  by case: ifP Z Nk=>// /eqP ->->.
suff : nilp s by move/nilP=>->.
rewrite /nilp eqn0Ngt -has_predT; apply/hasPn=>z Z.
move: (D z); rewrite inE Z orbT=>/(_ (erefl _)).
by case: ifP Z Nk=>// /eqP ->->.
Qed.

(* last_filter either returns default or a p-element of ks *)
Lemma last_filter_change k p (ks : seq A) :
        last k (filter p ks) != k ->
        p (last k (filter p ks)) && (last k (filter p ks) \in ks).
Proof. by move/last_change; rewrite mem_filter. Qed.

Lemma index_filter_mono (p : pred A) (ks : seq A) x y :
        p x -> 
        index x ks <= index y ks ->
        index x (filter p ks) <= index y (filter p ks).
Proof.
move=>Px; elim: ks=>[|k ks IH] //=; case P : (p k)=>/=;
by case: ifP Px; case: ifP=>// _ /eqP <-; rewrite P.
Qed.

Lemma filter_sub (p1 p2 : pred A) (s : seq A) :
        subpred p1 p2 -> 
        {subset filter p1 s <= filter p2 s}.
Proof.
move=>S; rewrite (_ : filter p1 s = filter p1 (filter p2 s)).
- by apply: mem_subseq; apply: filter_subseq.
rewrite -filter_predI; apply: eq_in_filter=>x X /=.
by case E : (p1 x)=>//=; rewrite (S _ E).
Qed.

Lemma last_filter_neq (p1 p2 : pred A) x (s : seq A) :
        subpred p1 p2 -> 
        x \notin s ->
        last x (filter p1 s) != x -> 
        last x (filter p2 s) != x.
Proof.
move=>S N /last_filter_change /andP [H1 H2].
apply: (@last_notin (last x [seq x <-s | p1 x])).
- by rewrite mem_filter H2 andbT; apply: S.
by rewrite mem_filter negb_and N orbT.
Qed.

Lemma last_filter_eq (p1 p2 : pred A) x (s : seq A) :
        subpred p1 p2 -> 
        x \notin s ->
        last x (filter p2 s) = x -> 
        last x (filter p1 s) = x.
Proof.
move=>S N /eqP E; apply/eqP.
by apply: contraTT E; apply: last_filter_neq.
Qed.

Lemma index_last_sub (p1 p2 : pred A) x (s : seq A) :
        subpred p1 p2 -> uniq (x :: s) ->
        index (last x (filter p1 s)) (x :: s) <=
        index (last x (filter p2 s)) (x :: s).
Proof.
move=>S; elim: s x=>[|k s IH] //= x; rewrite !inE negb_or -andbA.
rewrite -(eq_sym k) -!(eq_sym (last _ _)); case/and4P=>N Sx Sk U.
have [Ux Uk] : uniq (x :: s) /\ uniq (k :: s) by rewrite /= Sx Sk U.
case P1 : (p1 k)=>/=.
- rewrite (S _ P1) /=; case: (last k _ =P k).
  - move/last_nochange; rewrite mem_filter (negbTE Sk) andbF /=.
    move/eqP=>-> /=; rewrite (negbTE N).
    case: (last k _ =P k); first by move=>->; rewrite (negbTE N).
    by case/eqP/last_filter_change/andP; case: eqP Sx=>// <- /negbTE ->.
  move/eqP=>N1; move: (last_filter_neq S Sk N1)=>N2.
  move: (IH _ Uk); rewrite /= !(eq_sym k).
  rewrite (negbTE N1) (negbTE N2) -(last_changeE1 N1 x) -(last_changeE1 N2 x).
  rewrite (negbTE (last_changeE2 N1 _)) ?(mem_filter,negb_and,Sx,orbT) //.
  by rewrite (negbTE (last_changeE2 N2 _)) ?(mem_filter,negb_and,Sx,orbT).
case P2 : (p2 k)=>/=.
- case: (last x _ =P x)=>// /eqP N1; move: (last_filter_neq S Sx N1)=>N2.
  move: (IH _ Ux); rewrite /= !(eq_sym x) (negbTE N1) (negbTE N2).
  rewrite -(last_changeE1 N1 k) {1 3}(last_changeE1 N2 k).
  rewrite (negbTE (last_changeE2 N1 _)) ?(mem_filter,negb_and,Sk,orbT) //.
  by rewrite !(negbTE (last_changeE2 N2 _)) ?(mem_filter,negb_and,Sk,Sx,orbT).
case: (last x _ =P x)=>// /eqP N1; move: (last_filter_neq S Sx N1)=>N2.
move: (IH _ Ux); rewrite /= !(eq_sym x) (negbTE N1) (negbTE N2).
rewrite -(last_changeE1 N1 k) -(last_changeE1 N2 k).
rewrite (negbTE (last_changeE2 N1 _)) ?(mem_filter,negb_and,Sk,orbT) //.
by rewrite !(negbTE (last_changeE2 N2 _)) ?(mem_filter,negb_and,Sk,orbT).
Qed.

Lemma last_filter_last_helper (p : pred A) x (s : seq A) y :
        uniq (x :: s) -> 
        p y -> 
        y \in s ->
        index y s <= index (last x (filter p s)) s.
Proof.
elim: s x=>[|k s IH] x //=; rewrite !inE !negb_or !(eq_sym _ k).
case/andP=>/andP [H1 H2] /andP [H3 H4] Px.
case: eqP=> [->|_] //= Ks; case P: (p k)=>/=.
- case: eqP=>E; last by apply: IH=>//=; rewrite H3 H4.
  move: (@last_in y k (filter p s)); rewrite -E !mem_filter.
  by rewrite Px Ks P (negbTE H3); move/(_ (erefl _)).
case: eqP=>E; last by apply: IH=>//=; rewrite H2 H4.
by move: H1; rewrite E; move/last_filter_change; rewrite -E P.
Qed.

Lemma last_filter_last (p : pred A) x (s : seq A) y :
        uniq (x :: s) -> 
        p y -> 
        y \in s ->
        index y (x :: s) <= index (last x (filter p s)) (x :: s).
Proof.
move=>/= /andP [Sx U] H Sy /=; case: (x =P y)=>//= _.
have Hy : y \in [seq x <- s | p x] by rewrite mem_filter H Sy.
rewrite eq_sym; case: (last x _ =P x); last first.
- by move=>_; apply: last_filter_last_helper=>//=; rewrite Sx U.
move/last_nochange; rewrite mem_filter (negbTE Sx) andbF /=.
by move/eqP=>E; rewrite E in Hy.
Qed.

Lemma index_filter_ltL (p : pred A) (ks : seq A) (t1 t2 : A) :
         (t1 \notin ks) || p t1 ->
         (index t1 ks < index t2 ks) ->
         (index t1 (filter p ks) < index t2 (filter p ks)).
Proof.
elim: ks t1 t2=>[|k ks IH] t1 t2 //=; rewrite inE negb_or (eq_sym t1).
case: eqP=>[->{k} /= Pt1|/eqP Nkt1 /= H].
- by rewrite Pt1 /= eqxx; case: eqP.
case: eqP=>// /eqP Nkt2; case: ifP=>H1 /=.
- by rewrite (negbTE Nkt1) (negbTE Nkt2) !ltnS; apply: IH H.
by rewrite ltnS; apply: IH H.
Qed.

Lemma index_filter_leL (p : pred A) (ks : seq A) (t1 t2 : A) :
         (t1 \notin ks) || p t1 ->
         (index t1 ks <= index t2 ks) ->
         (index t1 (filter p ks) <= index t2 (filter p ks)).
Proof.
elim: ks t1 t2=>[|k ks IH] t1 t2 //=; rewrite inE negb_or (eq_sym t1).
case: eqP=>[->{k} /= Pt1|/eqP Nkt1 /= H].
- by rewrite Pt1 /= eqxx; case: eqP.
case: eqP=>// /eqP Nkt2; case: ifP=>H1 /=.
- by rewrite (negbTE Nkt1) (negbTE Nkt2) !ltnS; apply: IH H.
by rewrite ltnS; apply: IH H.
Qed.

Lemma index_filter_ltR (p : pred A) (ks : seq A) (t1 t2 : A) :
         (t2 \notin ks) || p t2 ->
         (index t1 (filter p ks) < index t2 (filter p ks)) ->
         (index t1 ks < index t2 ks).
Proof.
elim: ks t1 t2=>[|k ks IH] t1 t2 //=; rewrite inE negb_or /=.
rewrite (eq_sym t2).
case: eqP=>[->{k} /= Pt2|/eqP Nkt2 /=].
- by rewrite Pt2 /= eqxx; case: eqP.
case: eqP=>[->{t1}//|/eqP Nt1k].
case: ifP=>H1 H2 /=.
- by rewrite (negbTE Nt1k) (negbTE Nkt2) !ltnS; apply: IH H2.
by rewrite ltnS; apply: IH H2.
Qed.

Lemma index_filter_leR (p : pred A) (ks : seq A) (t1 t2 : A) :
         (t2 \notin ks) || p t2 ->
         (index t1 (filter p ks) <= index t2 (filter p ks)) ->
         (index t1 ks <= index t2 ks).
Proof.
elim: ks t1 t2=>[|k ks IH] t1 t2 //=; rewrite inE negb_or /=.
rewrite (eq_sym t2).
case: eqP=>[->{k} /= Pt2|/eqP Nkt2 /=].
- by rewrite Pt2 /= eqxx; case: eqP.
case: eqP=>[->{t1}//|/eqP Nt1k].
case: ifP=>H1 H2 /=.
- by rewrite (negbTE Nt1k) (negbTE Nkt2) !ltnS; apply: IH H2.
by rewrite ltnS; apply: IH H2.
Qed.

(* we can put the left and right lemmas together *)
Lemma index_filter_lt (p : pred A) (ks : seq A) (t1 t2 : A) :
         (t1 \notin ks) || p t1 -> 
         (t2 \notin ks) || p t2 ->
         (index t1 (filter p ks) < index t2 (filter p ks)) =
         (index t1 ks < index t2 ks).
Proof.
move=>H1 H2; apply/idP/idP.
- by apply: index_filter_ltR.
by apply: index_filter_ltL.
Qed.

Lemma index_filter_le (p : pred A) (ks : seq A) (t1 t2 : A) :
         (t1 \notin ks) || p t1 -> 
         (t2 \notin ks) || p t2 ->
         (index t1 (filter p ks) <= index t2 (filter p ks)) =
         (index t1 ks <= index t2 ks).
Proof.
move=>H1 H2; apply/idP/idP.
- by apply: index_filter_leR.
by apply: index_filter_leL.
Qed.

(* index and masking *)

Lemma index_mask (s : seq A) m a b  :
         uniq s ->
         a \in mask m s -> 
         b \in mask m s ->
         index a (mask m s) < index b (mask m s) <->
         index a s < index b s.
Proof.
elim: m s=>[|x m IH][|k s] //= /andP [K U]; case: x=>[|Ma Mb] /=.
- rewrite !inE; case/orP=>[/eqP <-|Ma].
  - by case/orP=>[/eqP ->|]; rewrite eqxx //; case: eqP.
  case/orP=>[/eqP ->|Mb]; first by rewrite eqxx.
  by case: eqP; case: eqP=>//; rewrite ltnS IH.
case: eqP Ma K=>[-> /mem_mask -> //|Ka].
case: eqP Mb=>[-> /mem_mask -> //|Kb Mb Ma].
by rewrite ltnS IH.
Qed.

Lemma indexlast_mask (s : seq A) m a b  :
         uniq s ->
         a \in mask m s -> 
         b \in mask m s ->
         indexlast a (mask m s) < indexlast b (mask m s) <->
         indexlast a s < indexlast b s.
Proof.
elim: m s=>[|x m IH][|k s] //= /andP [K U]; case: x=>[|Ma Mb] /=;
rewrite !indexlast_cons.
- rewrite !inE; case/orP=>[/eqP Ea|Ma].
  - rewrite -{k}Ea in K *.
    have Km: (a \notin mask m s) by apply: contra K; apply: mem_mask.
    case/orP=>[/eqP ->|]; rewrite eqxx /=; first by rewrite K ltnn.
    case: eqP=>[->|Nab] H /=; first by rewrite !ltnn.
    by rewrite K Km.
  case/orP=>[/eqP Eb|Mb].
  - rewrite -{k}Eb in K *.
    have ->: (b \notin mask m s) by apply: contra K; apply: mem_mask.
    by rewrite eqxx /= K.
  rewrite Ma Mb (mem_mask Ma) (mem_mask Mb) /= !andbF.
  by apply: IH.
case: eqP Ma K=>[-> /mem_mask -> //|Ka] /=.
case: eqP Mb=>[-> /mem_mask -> //|Kb Mb Ma _] /=.
by rewrite ltnS IH.
Qed.

Lemma index_subseq (s1 s2 : seq A) a b :
        subseq s1 s2 -> 
        uniq s2 -> 
        a \in s1 -> 
        b \in s1 ->
        index a s1 < index b s1 <-> index a s2 < index b s2.
Proof. by case/subseqP=>m _ ->; apply: index_mask. Qed.

Lemma indexlast_subseq (s1 s2 : seq A) a b :
        subseq s1 s2 -> 
        uniq s2 -> 
        a \in s1 -> 
        b \in s1 ->
        indexlast a s1 < indexlast b s1 <-> indexlast a s2 < indexlast b s2.
Proof. by case/subseqP=>m _ ->; apply: indexlast_mask. Qed.

End FilterLastIndex.

(* index and mapping *)

Section IndexPmap.
Variables (A B : eqType).

Lemma index_pmap_inj (s : seq A) (f : A -> option B) a1 a2 b1 b2 :
        injective f -> 
        f a1 = Some b1 -> 
        f a2 = Some b2 ->
        index b1 (pmap f s) < index b2 (pmap f s) <-> index a1 s < index a2 s.
Proof.
move=>Inj E1 E2; elim: s=>[|k s IH] //=; rewrite /oapp.
case: eqP=>[->{k}|].
- rewrite E1 /= eqxx.
  case: (a1 =P a2) E1 E2=>[-> -> [/eqP ->] //|].
  by case: (b1 =P b2)=>[-> Na <- /Inj /esym/Na|].
case: eqP=>[->{k} Na|N2 N1]; first by rewrite E2 /= eqxx !ltn0.
case E : (f k)=>[b|] //=.
case: eqP E1 E=>[-><- /Inj/N1 //|_ _].
by case: eqP E2=>[-><- /Inj/N2 //|_ _ _]; rewrite IH.
Qed.

Lemma index_pmap_inj_mem (s : seq A) (f : A -> option B) a1 a2 b1 b2 :
        {in s &, injective f} ->
        a1 \in s -> 
        a2 \in s ->
        f a1 = Some b1 -> 
        f a2 = Some b2 ->
        index b1 (pmap f s) < index b2 (pmap f s) <-> index a1 s < index a2 s.
Proof.
move=>Inj A1 A2 E1 E2.
elim: s Inj A1 A2=>[|k s IH] //= Inj; rewrite /oapp !inE !(eq_sym k).
case: eqP Inj=>[<-{k} /= Inj _|].
- rewrite E1 /= !eqxx eq_sym.
  case: eqP E1 E2=>[->-> [->]|]; first by rewrite eqxx.
  case: eqP=>[-> Na <- E /= A2|//].
  by move/Inj: E Na=>-> //; rewrite inE ?(eqxx,A2,orbT).
case eqP=>[<-{k} Na Inj /= A1 _|]; first by rewrite E2 /= eqxx !ltn0.
move=>N2 N1 Inj /= A1 A2.
have Inj1 : {in s &, injective f}.
- by move=>x y X Y; apply: Inj; rewrite inE ?X ?Y ?orbT.
case E : (f k)=>[b|] /=; last by rewrite IH.
case: eqP E1 E=>[-> <- E|_ _].
- by move/Inj: E N1=>-> //; rewrite inE ?(eqxx,A1,orbT).
case: eqP E2=>[-><- E|_ _ _]; last by rewrite IH.
by move/Inj: E N2=>-> //; rewrite inE ?(eqxx,A2,orbT).
Qed.

(* we can relax the previous lemma a bit *)
(* the relaxation will be more commonly used than the previous lemma *)
(* because the option type gives us the implication that the second *)
(* element is in the map *)
Lemma index_pmap_inj_in (s : seq A) (f : A -> option B) a1 a2 b1 b2 :
        {in s & predT, injective f} ->
        f a1 = Some b1 -> 
        f a2 = Some b2 ->
        index b1 (pmap f s) < index b2 (pmap f s) <-> index a1 s < index a2 s.
Proof.
move=>Inj E1 E2.
case A1 : (a1 \in s); last first.
- move/negbT/index_sizeE: (A1)=>->.
  suff /index_sizeE -> : b1 \notin pmap f s by rewrite !ltnNge !index_size.
  rewrite mem_pmap; apply/mapP; case=>x X /esym; rewrite -E1=>E.
  by move/(Inj _ _ X): E A1=><- //; rewrite X.
case A2 : (a2 \in s).
- by apply: index_pmap_inj_mem=>// x y X _; apply: Inj.
move/negbT/index_sizeE: (A2)=>->.
suff /index_sizeE -> : b2 \notin pmap f s.
- by rewrite !index_mem /= A1 mem_pmap; split=>// _; apply/mapP; exists a1.
rewrite mem_pmap; apply/mapP; case=>x X /esym; rewrite -E2=>E.
by move/(Inj _ _ X): E A2=><- //; rewrite X.
Qed.

End IndexPmap.

Section SeqRel.
Variable (A : eqType).
Implicit Type (ltT leT : rel A).

(* ordering with path, seq and last *)

Lemma eq_last (s : seq A) x y :
        x \in s -> 
        last y s = last x s.
Proof. by elim: s x y=>[|w s IH]. Qed.

Lemma seq_last_in (s : seq A) x :
        last x s \notin s -> 
        s = [::].
Proof.
case: (lastP s)=>{s} // s y; case: negP=>//; elim; rewrite last_rcons.
by elim: s=>[|y' s IH]; rewrite /= inE // IH orbT.
Qed.

Lemma path_last (s : seq A) leT x :
        transitive leT -> 
        path leT x s ->
        (x == last x s) || leT x (last x s).
Proof.
move=>T /(order_path_min T) /allP; case: s=>[|a s] H /=.
- by rewrite eqxx.
by rewrite (H (last a s)) ?orbT // mem_last.
Qed.

Lemma path_lastR (s : seq A) leT x :
        reflexive leT -> 
        transitive leT ->
        path leT x s -> 
        leT x (last x s).
Proof. by move=>R T P; case: eqP (path_last T P)=>// <- _; apply: R. Qed.

(* in a sorted list, the last element is maximal *)
(* and the maximal element is last *)

Lemma sorted_last_key_max (s : seq A) leT x y :
        transitive leT -> 
        sorted leT s -> 
        x \in s ->
        (x == last y s) || leT x (last y s).
Proof.
move=>T; elim: s x y=>[|z s IH] //= x y H; rewrite inE.
case: eqP=>[->|] /= _; first by apply: path_last.
by apply: IH (path_sorted H).
Qed.

Lemma sorted_last_key_maxR (s : seq A) leT x y :
        reflexive leT -> 
        transitive leT ->
        sorted leT s -> 
        x \in s -> 
        leT x (last y s).
Proof.
move=>R T S X; case/orP: (sorted_last_key_max y T S X)=>// /eqP <-.
by apply: R.
Qed.

Lemma sorted_max_key_last (s : seq A) leT x y :
        transitive leT -> 
        antisymmetric leT ->
        sorted leT s -> 
        x \in s ->
        (forall z, z \in s -> leT z x) -> 
        last y s = x.
Proof.
move=>T S; elim: s x y => [|w s IH] //= x y; rewrite inE /=.
case: eqP=>[<- /= H1 _ H2 | _ H /= H1 H2]; last first.
- apply: IH (path_sorted H) H1 _ => z H3; apply: H2.
  by rewrite inE /= H3 orbT.
case/orP: (path_last T H1)=>[/eqP //|] X.
by apply: S; rewrite X H2 ?mem_last.
Qed.

Lemma max_key_last_notin (s : seq A) (leT : rel A) x y :
        leT y x -> 
        (forall z, z \in s -> leT z x) -> 
        leT (last y s) x.
Proof.
elim: s x y=>[|w s IH] //= x y H1 H2; apply: IH.
- by apply: (H2 w); rewrite inE eqxx.
by move=>z D; apply: H2; rewrite inE D orbT.
Qed.

Lemma seq_last_mono (s1 s2 : seq A) leT x :
        transitive leT -> 
        path leT x s1 -> 
        path leT x s2 ->
        {subset s1 <= s2} ->
        (last x s1 == last x s2) || leT (last x s1) (last x s2).
Proof.
move=>T; case: s1=>/= [_ H1 _|a s]; first by apply: path_last H1.
case/andP=>H1 H2 H3 H; apply: sorted_last_key_max (path_sorted H3) _=>//.
apply: {x s2 H1 H3} H; rewrite inE orbC -implyNb.
by case E: (_ \notin _) (@seq_last_in s a)=>//= ->.
Qed.

Lemma seq_last_monoR (s1 s2 : seq A) leT x :
        reflexive leT -> 
        transitive leT ->
        path leT x s1 -> 
        path leT x s2 ->
        {subset s1 <= s2} ->
        leT (last x s1) (last x s2).
Proof. by move=>R T P1 P2 S; case: eqP (seq_last_mono T P1 P2 S)=>[->|]. Qed.

Lemma ord_path (s : seq A) leT (x y : A) :
        transitive leT ->
        leT x y -> 
        path leT y s -> 
        path leT x s.
Proof.
move=>T; elim: s x y=>[|k s IH] x y //= H1 /andP [H2 ->].
by rewrite (T _ _ _ H1 H2).
Qed.

Lemma path_mem (s : seq A) leT x y :
        transitive leT ->
        path leT x s -> 
        y \in s -> 
        leT x y.
Proof.
move=>T; elim: s x=>[|z s IH] x //= /andP [O P].
rewrite inE; case/orP=>[/eqP -> //|].
by apply: IH; apply: ord_path O P.
Qed.

Lemma path_mem_irr (s : seq A) ltT x :
        irreflexive ltT -> 
        transitive ltT ->
        path ltT x s -> 
        x \notin s.
Proof.
move=>I T P; apply: contraFT (I x).
by rewrite negbK; apply: path_mem T P.
Qed.

Lemma sorted_rcons (s : seq A) leT (y : A) :
        sorted leT s -> 
        (forall x, x \in s -> leT x y) ->
        sorted leT (rcons s y).
Proof.
elim: s=>[|a s IH] //= P H; rewrite rcons_path P /=.
by apply: H (mem_last _ _).
Qed.

Lemma sorted_subset_subseq (s1 s2 : seq A) ltT :
        irreflexive ltT -> 
        transitive ltT ->
        sorted ltT s1 -> 
        sorted ltT s2 ->
        {subset s1 <= s2} -> 
        subseq s1 s2.
Proof.
move=>R T S1 S2 H.
suff -> : s1 = filter (fun x => x \in s1) s2 by apply: filter_subseq.
apply: irr_sorted_eq S1 _ _=>//; first by rewrite sorted_filter.
by move=>k; rewrite mem_filter; case S : (_ \in _)=>//; rewrite (H _ S).
Qed.

Lemma sorted_ord_index (s : seq A) ltT x y :
        irreflexive ltT -> 
        transitive ltT ->
        sorted ltT s -> 
        x \in s -> 
        ltT x y -> 
        index x s < index y s.
Proof.
move=>I T S P H; elim: s S P=>[|z s IH] //= P; rewrite !inE !(eq_sym z).
case: eqP H P=>[<-{z} H P _|_ H P /= X]; first by case: eqP H=>[<-|] //; rewrite I.
case: eqP H P=>[<-{z} H|_ H]; last first.
- by move/path_sorted=>S; rewrite ltnS; apply: IH.
by move/(path_mem T)/(_ X)=>/(T _ _ _ H); rewrite I.
Qed.

Lemma path_ord_index_leq (s : seq A) leT x y :
        transitive leT -> 
        antisymmetric leT ->
        leT x y -> 
        path leT y s -> 
        x \in s -> 
        x = y.
Proof.
move=>T; elim: s x y=>[|a l IH] //= x y As Lxy.
case/andP=>Lya Pal; rewrite inE.
case: eqP Lya Pal As=>[<-{a} Lyx _ As _|Nxa Lya Pal /= As' X].
- by apply: As=>//; rewrite Lxy Lyx.
by move/Nxa: (IH x a As' (T _ _ _ Lxy Lya) Pal X).
Qed.

Lemma sorted_ord_index_leq (s : seq A) leT x y :
        transitive leT -> 
        antisymmetric leT ->
        sorted leT s ->
        x \in s -> 
        leT x y -> 
        x != y -> 
        index x s < index y s.
Proof.
move=>T As S P H N; elim: s S As P=>[|z s IH] //= P As; rewrite inE !(eq_sym z).
case: eqP H P As=>[<-{z} H P As _|Nxz H P As /= X]; first by rewrite eq_sym (negbTE N).
case: eqP Nxz P=>[<-{z} Nxy P|Nyz Nxz P].
- by move/Nxy: (path_ord_index_leq T As H P X).
by apply: IH X=>//; apply: path_sorted P.
Qed.

Lemma sorted_index_ord (s : seq A) leT x y :
        transitive leT -> 
        sorted leT s -> 
        y \in s ->
        index x s < index y s -> 
        leT x y.
Proof.
move=>T; elim: s=>[|z s IH] //= P; rewrite inE !(eq_sym z).
case: eqP=>//= /eqP N; case: eqP P=>[-> P /(path_mem T P)|_ P] //.
by rewrite ltnS; apply: IH; apply: path_sorted P.
Qed.

(* sorted, uniq, filter *)

Lemma lt_sorted_uniq_le (s : seq A) ltT :
        irreflexive ltT ->
        antisymmetric ltT ->
        transitive ltT ->
        sorted ltT s = uniq s && 
        (sorted (fun k t => (k == t) || ltT k t) s).
Proof.
move=>I As T; case: s=>// n s; elim: s n=>//= m s IHs n.
rewrite inE negb_or IHs -!andbA /=.
case: (n =P m)=>[->|/eqP Nm /=]; first by rewrite I.
case lTnm : (ltT n m)=>/=; last by rewrite !andbF.
case Ns: (n \in s)=>//=; do !bool_congr.
have T' : transitive (fun k t => (k == t) || ltT k t).
- move=>x y z /orP [/eqP -> //|H].
  case/orP=>[/eqP <-|]; first by rewrite H orbT.
  by move/(T _ _ _ H)=>->; rewrite orbT.
apply/negP=>/(order_path_min T')/allP/(_ n Ns).
rewrite eq_sym (negbTE Nm) /= =>lTmn.
by rewrite (As m n) ?eqxx // lTnm lTmn in Nm.
Qed.

Lemma sort_sorted_in_lt (s : seq A) ltT :
        irreflexive ltT ->
        antisymmetric ltT ->
        transitive ltT ->
        uniq s ->
        {in s &, total (fun k t => (k == t) || ltT k t)} ->
        sorted ltT (sort (fun k t => (k == t) || ltT k t) s).
Proof.
move=>I S T U Tot; rewrite lt_sorted_uniq_le //.
by rewrite sort_uniq U (sort_sorted_in Tot _).
Qed.

(* filtering and consecutive elements in an order *)
Lemma filterCN (ltT : rel A) f t1 t2 :
       t1 \notin f ->
       {in f, forall z, ltT z t2 = (z == t1) || ltT z t1} ->
       filter (ltT^~ t2) f = filter (ltT^~ t1) f.
Proof.
move=>N C; apply: eq_in_filter=>x T; rewrite C ?inE ?orbT //.
by case: eqP N T=>// -> /negbTE ->.
Qed.

Lemma filterCE (ltT : rel A) f t1 t2 :
        irreflexive ltT ->
        transitive ltT ->
        sorted ltT f ->
        {in f, forall z, ltT z t2 = (z == t1) || ltT z t1} ->
        t1 \in f ->
        filter (ltT^~ t2) f = filter (ltT^~ t1) f ++ [:: t1].
Proof.
move=>I T S Z F; have U : uniq f by apply: sorted_uniq T I _ S.
rewrite -(filter_pred1_uniq U F); apply: irr_sorted_eq (T) I _ _ _ _ _.
- by apply: sorted_filter T _ _ S.
- rewrite -[filter (ltT^~ t1) _]revK -[filter (pred1 t1) _]revK -rev_cat.
  rewrite rev_sorted -filter_rev filter_pred1_uniq ?(mem_rev,rev_uniq) //.
  rewrite /= path_min_sorted ?(rev_sorted, sorted_filter T _ S) //.
  by apply/allP=>x; rewrite mem_rev mem_filter=>/andP [].
move=>x; rewrite mem_cat !mem_filter /=.
case X: (x \in f); last by rewrite !andbF.
by rewrite Z // orbC !andbT.
Qed.

(* frequently we have nested filtering and sorting *)
(* for which the following forms of the lemmas is more effective *)

Lemma filter2CN (ltT : rel A) p f t1 t2 :
       t1 \notin p ->
       {in p, forall z, ltT z t2 = (z == t1) || ltT z t1} ->
       filter (ltT^~ t2) (filter p f) = filter (ltT^~ t1) (filter p f).
Proof.
move=>N C; apply: filterCN; first by rewrite mem_filter negb_and N.
by move=>z; rewrite mem_filter=>/andP [D _]; apply: C.
Qed.

Lemma filter2CE (ltT : rel A) (p : pred A) f t1 t2 :
       irreflexive ltT ->
       antisymmetric ltT ->
       transitive ltT ->
       {in f &, total (fun k t => (k == t) || ltT k t)} ->
       {in p, forall z, ltT z t2 = (z == t1) || ltT z t1} ->
       uniq f ->
       p t1 -> t1 \in f ->
       filter (ltT^~ t2)
         (filter p (sort (fun k t => (k == t) || ltT k t) f)) =
       filter (ltT^~ t1)
         (filter p (sort (fun k t => (k == t) || ltT k t) f)) ++ [:: t1].
Proof.
move=>I Asym T Tot Z U P F; apply: filterCE (I) (T) _ _ _.
- by rewrite (sorted_filter T _ _) //; apply: sort_sorted_in_lt.
- by move=>z; rewrite mem_filter=>/andP [Pz _]; apply: Z.
by rewrite mem_filter mem_sort P F.
Qed.

(* nth *)

Lemma nth_cons (a x : A) (s : seq A) (n : nat) :
        nth a (x :: s) n = if n == 0 then x else nth a s n.-1.
Proof. by case: n. Qed.

Lemma nth_base (s : seq A) k1 k2 i :
        i < size s -> 
        nth k1 s i = nth k2 s i.
Proof.
elim: s i=>[|x xs IH] //= i K; rewrite !nth_cons.
by case: eqP=>//; case: i K=>// i; rewrite ltnS=>/IH ->.
Qed.

Lemma nth_path_head (s : seq A) leT x0 k i :
        transitive leT ->
        i <= size s -> 
        path leT k s ->
        (k == nth x0 (k::s) i) || leT k (nth x0 (k::s) i).
Proof.
move=>T; case: (posnP i)=>[->|N S P]; first by rewrite eqxx.
apply/orP; right; elim: i N S P=>[|i] //; case: s=>//= x xs IH _.
rewrite ltnS=>N /andP [H1 H2]; case: i IH N=>//= i /(_ (erefl _)) IH N.
rewrite !ltnS in IH; move: (IH (ltnW N)); rewrite H1 H2=>/(_ (erefl _)).
by move/T; apply; apply/pathP.
Qed.

Lemma nth_path_last (s : seq A) leT x0 k i :
        transitive leT ->
        i < size s -> path leT k s ->
        (nth x0 s i == last k s) || leT (nth x0 s i) (last k s).
Proof.
move=>T S P.
suff : forall z, z \in s -> (z == last k s) || leT z (last k s).
- by apply; rewrite mem_nth.
move=>z; apply: sorted_last_key_max=>//.
by apply: path_sorted P.
Qed.

Lemma nth_consS (s : seq A) x0 k i : nth x0 s i = nth x0 (k::s) i.+1.
Proof. by []. Qed.

Lemma nth_leT (s : seq A) leT x0 k i :
        i < size s -> 
        path leT k s ->
        leT (nth x0 (k::s) i) (nth x0 s i).
Proof.
elim: i k s=>[|i IH] k s; first by case: s=>[|x xs] //= _ /andP [].
by case: s IH=>[|x xs] //= IH N /andP [P1 P2]; apply: IH.
Qed.

Lemma nth_ltn_mono (s : seq A) leT x0 k i j :
        transitive leT ->
        i <= size s -> 
        j <= size s ->
        path leT k s ->
        i < j -> 
        leT (nth x0 (k::s) i) (nth x0 (k::s) j).
Proof.
move=>T S1 S2 P; elim: j S2=>[|j IH] //= S2.
move: (nth_leT x0 S2 P)=>L.
rewrite ltnS leq_eqVlt=>/orP; case=>[/eqP -> //|].
by move/(IH (ltnW S2))/T; apply.
Qed.

Lemma nth_mono_ltn (s : seq A) ltT x0 k i j :
         irreflexive ltT ->
         transitive ltT ->
         i <= size s -> 
         j <= size s ->
         path ltT k s ->
         ltT (nth x0 (k::s) i) (nth x0 (k::s) j) -> 
         i < j.
Proof.
move=>I T S1 S2 P; case: ltngtP=>//; last by move=>->; rewrite I.
by move/(nth_ltn_mono x0 T S2 S1 P)/T=>X /X; rewrite I.
Qed.

Lemma nth_between (s : seq A) ltT x0 k z i :
        irreflexive ltT ->
        transitive ltT ->
        path ltT k s ->
        ltT (nth x0 (k::s) i) z -> 
        ltT z (nth x0 s i) -> 
        z \notin s.
Proof.
move=>I T P H1 H2; apply/negP=>Z; move: H1 H2.
case: (leqP i (size s))=>N; last first.
- rewrite !nth_default ?(ltnW N) //= => H.
  by move/(T _ _ _ H); rewrite I.
have S : index z s < size s by rewrite index_mem.
rewrite -(nth_index x0 Z) !(nth_consS s x0 k).
move/(nth_mono_ltn I T N S P)=>K1.
move/(nth_mono_ltn I T S (leq_trans K1 S) P); rewrite ltnS.
by case: ltngtP K1.
Qed.

(* how to prove that something's sorted via index? *)

Lemma index_sorted (s : seq A) (leT : rel A) :
        uniq s ->
        (forall a b, a \in s -> b \in s -> 
           index a s < index b s -> leT a b) ->
        sorted leT s.
Proof.
elim: s=>[|x xs IH] //= U H; have P : all (leT x) xs.
- apply/allP=>z Z; apply: H; rewrite ?(inE,eqxx,Z,orbT) //.
  by case: ifP U=>// /eqP ->; rewrite Z.
rewrite (path_min_sorted P); apply: IH=>[|a b Xa Xb N]; first by case/andP: U.
apply: H; rewrite ?(inE,Xa,Xb,orbT) //.
by case: eqP U=>[->|]; case: eqP=>[->|]; rewrite ?(Xa,Xb).
Qed.

End SeqRel.

(* there always exists a nat not in a given list *)
Lemma not_memX (ks : seq nat) : exists k, k \notin ks.
Proof.
have L a xs : foldl addn a xs = a + foldl addn 0 xs.
- elim: xs a=>[|z xs IH] //= a; first by rewrite addn0.
  by rewrite add0n // [in LHS]IH [in RHS]IH addnA.
set k := foldl addn 1 ks.
suff K a : a \in ks -> a < k by exists k; apply/negP=>/K; rewrite ltnn.
rewrite {}/k; elim: ks=>[|k ks IH] //=; rewrite inE.
case/orP=>[/eqP ->|/IH]; first by rewrite L add1n addSn ltnS leq_addr.
rewrite L=>N; rewrite L; apply: leq_trans N _.
by rewrite addnAC leq_addr.
Qed.

Section BigCat.
Context {A B : Type}.
Implicit Types (xs : seq A) (f : A -> seq B).

Lemma flatten_map_big xs f :
        flatten (map f xs) = \big[cat/[::]]_(x <- xs) f x.
Proof.
elim: xs=>/= [|x xs IH]; first by rewrite big_nil.
by rewrite big_cons IH.
Qed.

Lemma size_big_cat xs f :
        size (\big[cat/[::]]_(x <- xs) f x) =
        \sum_(x <- xs) (size (f x)).
Proof.
elim: xs=>[|x xs IH] /=; first by rewrite !big_nil.
by rewrite !big_cons size_cat IH.
Qed.

Lemma has_big_cat (p : pred B) xs f :
        has p (\big[cat/[::]]_(x <- xs) f x) =
        has (fun x => has p (f x)) xs.
Proof.
elim: xs=>[|x xs IH]; first by rewrite big_nil.
by rewrite big_cons has_cat /= IH.
Qed.

End BigCat.

Lemma big_cat_mem_has A (B : eqType) xs (f : A -> seq B) b :
        b \in \big[cat/[::]]_(x <- xs) f x =
        has (fun x => b \in f x) xs.
Proof.
rewrite -has_pred1 has_big_cat; apply: eq_has=>x.
by rewrite has_pred1.
Qed.

(* big_cat_mem for A : Type *)
Lemma big_cat_memT A (B : eqType) x xs (f : A -> seq B) :
        reflect (exists2 i, i \In xs & x \in f i)
                (x \in \big[cat/[::]]_(i <- xs) f i).
Proof. by rewrite big_cat_mem_has; apply/hasPIn. Qed.

(* big_cat_mem for A : eqType *)
Lemma big_cat_memE (A B : eqType) x xs (f : A -> seq B) :
        reflect (exists2 i, i \in xs & x \in f i)
                (x \in \big[cat/[::]]_(i <- xs) f i).
Proof. by rewrite big_cat_mem_has; apply: hasP. Qed.

(* big_cat_mem for A : finType *)
Lemma big_cat_mem (A : finType) (B : eqType) (f : A -> seq B) x :
        reflect (exists i, x \in f i)
                (x \in \big[cat/[::]]_i f i).
Proof. 
case: big_cat_memE=>H; constructor.
- by case: H=>i H1 H2; exists i.
by case=>i X; elim: H; exists i.
Qed.

(* uniqueness for A : Type *)
Lemma uniq_big_catT A (B : eqType) xs (f : A -> seq B) :
        Uniq xs ->
        (forall x, x \In xs -> uniq (f x)) ->
        (forall x1 x2, x1 \In xs -> x2 \In xs -> 
          has (mem (f x1)) (f x2) -> x1 = x2) ->
        uniq (\big[cat/[::]]_(x <- xs) f x).
Proof.
elim: xs=>[|x xs IH] /=.
- by rewrite big_nil /=; constructor.
case=>Nx U H1 H2; rewrite big_cons cat_uniq.
apply/and3P; split.
- by apply: H1; left.
- rewrite has_big_cat -all_predC; apply/allPIn=>x3 H3 /=.
  by apply: contra_notN Nx=>H; rewrite (H2 _ _ _ _ H) //; [left | right].
apply: IH=>//.
- by move=>z Hz; apply: H1; right.
by move=>z1 z2 Hz1 Hz2 N; apply: H2=>//; right.
Qed.

Lemma big_cat_uniq_pairwise A (B : eqType) xs (f : A -> seq B) x1 x2 :
        uniq (\big[cat/[::]]_(x <- xs) f x) ->
        x1 \In xs -> 
        x2 \In xs -> 
        has (mem (f x1)) (f x2) ->
        x1 = x2.
Proof.
elim: xs=>[|x xs IH] //.
rewrite big_cons cat_uniq; case/and3P=>U N Us.
case/In_cons=>[->|H1]; case/In_cons=>[->|H2] //; last by apply: IH.
- case/hasP=>/= b Hb1 Hb2.
  exfalso; move/negP: N; apply; apply/hasP.
  by exists b=>//; apply/big_cat_memT; exists x2.
case/hasP=>/= b Hb1 Hb2.
exfalso; move/negP: N; apply.
apply/hasP; exists b=>//; apply/big_cat_memT.
by exists x1.
Qed.

(* uniqueness for A : eqType *)
Lemma uniq_big_catE (A B : eqType) (f : A -> seq B) (xs : seq A) :
        reflect
        [/\ forall i, i \in xs -> uniq (f i),
            forall i k, i \in xs -> k \in f i -> count_mem i xs = 1 &
            forall i j k, i \in xs -> j \in xs ->
              k \in f i -> k \in f j -> i = j]
        (uniq (\big[cat/[::]]_(i <- xs) f i)).
Proof.
elim: xs=>[|x xs IH] /=; first by rewrite big_nil; constructor.
rewrite big_cons cat_uniq.
case H1 : (uniq (f x))=>/=; last first.
- by constructor; case=>/(_ x); rewrite inE eqxx H1=>/(_ erefl).
case: hasPn=>/= V; last first.
- constructor; case=>H2 H3 H4; elim: V=>z /big_cat_memE [i X Zi].
  apply/negP=>Zx; move/(H3 i z): (Zi); rewrite inE X orbT=>/(_ erefl).
  move: (H4 x i z); rewrite !inE eqxx X orbT=>/(_ erefl erefl Zx Zi)=>E.
  by rewrite -{i Zi}E eqxx add1n in X *; case=>/count_memPn; rewrite X.
case: IH=>H; constructor; last first.
- case=>H2 H3 H4; apply: H; split; last 1 first.
  - by move=>i j k Xi Xj; apply: H4; rewrite inE ?Xi ?Xj orbT.
  - by move=>i X; apply: H2; rewrite inE X orbT.
  move=>i k X D; move/(H3 i k): (D); rewrite inE X orbT=>/(_ erefl).
  case: (x =P i) X D=>[<-{i}|N] X D; last by rewrite add0n.
  by rewrite add1n=>[[]] /count_memPn; rewrite X.
case: H=>H2 H3 H4; split; first by move=>i; rewrite inE=>/orP [/eqP ->|/H2].
- move=>i k; rewrite inE eq_sym; case: (x =P i)=>[<- _|N /= Xi] K; last first.
  - by rewrite add0n; apply: H3 Xi K.
  rewrite add1n; congr S; apply/count_memPn; apply: contraL (K)=>X.
  by apply/V/big_cat_memE; exists x.
move=>i j k; rewrite !inE=>/orP [/eqP ->{i}|Xi] /orP [/eqP ->{j}|Xj] Ki Kj //.
- by suff : k \notin f x; [rewrite Ki | apply/V/big_cat_memE; exists j].
- by suff : k \notin f x; [rewrite Kj | apply/V/big_cat_memE; exists i].
by apply: H4 Kj.
Qed.

(* alternative formulation *)
Lemma uniq_big_catEX (A B : eqType) (f : A -> seq B) (xs : seq A) :
        uniq xs ->
        reflect
        [/\ forall i, i \in xs -> uniq (f i) &
            forall i j k, i \in xs -> j \in xs ->
              k \in f i -> k \in f j -> i = j]
        (uniq (\big[cat/[::]]_(i <- xs) f i)).
Proof.
move=>U; case: uniq_big_catE=>H; constructor; first by case: H.
by case=>H1 H2; elim: H; split=>// i k I K; rewrite count_uniq_mem // I.
Qed.

(* uniqueness for A : finType *)
Lemma uniq_big_cat (A : finType) (B : eqType) (f : A -> seq B) :
        reflect ([/\ forall t, uniq (f t) &
                     forall t1 t2 k, k \in f t1 -> k \in f t2 -> t1 = t2])
                (uniq (\big[cat/[::]]_tag f tag)).
Proof.
case: uniq_big_catEX=>[|[R1 R2]|R].
- by rewrite /index_enum -enumT enum_uniq.
- by constructor; split=>[t|t1 t2 k K1 K2]; [apply: R1|apply: R2 K1 K2].
constructor; case=>R1 R2; elim: R; split=>[t ?|t1 t2 k ??];
by [apply: R1 | apply: R2].
Qed.

Lemma uniq_big_cat_uniqT A (B : eqType) xs (f : A -> seq B) y :
        uniq (\big[cat/[::]]_(x <- xs) f x) ->
        y \In xs -> 
        uniq (f y).
Proof.
elim: xs=>[|x xs IH] in y * => //.
rewrite big_cons InE cat_uniq.
case/and3P=>U _ Us; case=>[->|Hy] //.
by apply: IH.
Qed.

Prenex Implicits uniq_big_cat_uniqT.

Lemma uniq_big_cat_uniq (A : finType) (f : A -> seq nat) t : 
        uniq (\big[cat/[::]]_t f t) -> 
        uniq (f t).
Proof. by move/uniq_big_cat_uniqT; apply; apply/mem_seqP. Qed.

Lemma uniq_big_cat_uniq0 (A : finType) (f : A -> seq nat) t : 
        uniq (0 :: \big[cat/[::]]_t f t) -> uniq (0 :: f t).
Proof.
case/andP=>U1 /uniq_big_cat_uniq /= U2.
rewrite U2 andbT (contra _ U1) // => U3.
by apply/big_cat_mem; exists t.
Qed.

Lemma uniq_big_cat_disj (A : finType) (B : eqType) (f : A -> seq B) t1 t2 x : 
         uniq (\big[cat/[::]]_t f t) ->
         x \in f t1 -> 
         x \in f t2 -> 
         t1 = t2.
Proof. by case/uniq_big_cat=>_; apply. Qed.


