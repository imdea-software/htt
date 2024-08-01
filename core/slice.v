(*
Copyright 2022 IMDEA Software Institute
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
From mathcomp Require Import ssrnat eqtype seq path interval order.
From mathcomp Require Import fintype finfun tuple.
From pcm Require Import options prelude seqext.

Open Scope order_scope.
Import Order.Theory.

(* DEVCOMMENT *)
(* intervals used to do these simplifications automatically *)
(* but that changed with mathcomp 2.0 *)
(* /DEVCOMMENT *)
Section BSimp_Extension.
Variables (disp : unit) (T : porderType disp).
Implicit Types (x y : T) (b c : bool).

Lemma binf_inf b c : (BInfty T b == BInfty T c) = (b == c).
Proof. by rewrite eqE /= eqE /= andbT. Qed.

Lemma bside_inf x b c : 
        ((BSide b x == BInfty T c) = false) * 
        ((BInfty T c == BSide b x) = false).
Proof. by rewrite !eqE /= !eqE /= !andbF. Qed.

Lemma bside_side x y b c :
        (BSide b x == BSide c y) = (b == c) && (x == y).
Proof. by rewrite !eqE. Qed.

End BSimp_Extension.

Definition bnd_simp := ((@bside_inf, @binf_inf, @bside_side), bnd_simp).

(* sequence slicing by nat indices *)
(* reuses mathcomp interval infrastructure *)

(* convert bound to nat *)
(* maps -oo -> 0, +oo -> m *)
Definition bnd (i : itv_bound nat) (m : nat) : nat :=
  match i with
  | BSide  b n => n + ~~ b
  | BInfty b   => if b then 0 else m
  end.

(* slicing is applying an interval to a seq *)
Definition slice {A : Type} (s : seq A) (i : interval nat) :=
  let sz := size s in
  let: Interval l u := i in
  drop (bnd l sz) (take (bnd u sz) s).

Arguments slice {A} s i : simpl never.

Notation "&: s i" := (slice s i)
 (at level 1, i at next level, s at next level,
  format "'&:' s  i") : fun_scope.

(* subtract n from bound, convert values past zero to -oo *)
Definition shl_bnd (i : itv_bound nat) (n : nat) :=
  match i with
  | BSide  b m => if (m < n)%N then -oo else BSide b (m - n)
  | BInfty b => BInfty _ b
  end.

Lemma shl_bnd0 i : shl_bnd i 0%N = i.
Proof. by case: i=>[[] i|[]] //=; rewrite subn0. Qed.

Lemma shl_bnd_add i n m : shl_bnd (shl_bnd i n) m = shl_bnd i (n+m).
Proof.
case: i=>[[] i|[]] //=.
- case: ltnP=>Hin /=; first by rewrite ltn_addr.
  by rewrite ltn_subLR // subnDA.
case: ltnP=>Hin /=; first by rewrite ltn_addr.
by rewrite ltn_subLR // subnDA.
Qed.

Definition shl_itv (i : interval nat) (n : nat) :=
  let: Interval l u := i in
  Interval (shl_bnd l n) (shl_bnd u n).

Lemma shl_itv0 i : shl_itv i 0%N = i.
Proof. by case: i=>i j /=; rewrite !shl_bnd0. Qed.

Lemma shl_itv_add i n m : shl_itv (shl_itv i n) m = shl_itv i (n+m).
Proof. by case: i=>i j /=; rewrite !shl_bnd_add. Qed.

Lemma mem_shl n m i :
  (n \in shl_itv i m) = (m + n \in i).
Proof.
rewrite !in_itv; case: i=>i j /=.
case: i=>[l i|[]]; case: j=>[r j|[]] //=;
rewrite ?andbF ?andbT //.
- case: (ltnP j m)=>/= Hj.
  - rewrite andbF; symmetry; apply/negbTE; rewrite negb_and lteifNE negbK -lteifNE.
    by apply/orP; right; apply/lteifS/ltn_addr.
  have ->: (n < j - m ?<= if ~~ r) = (m + n < j ?<= if ~~ r).
  - case: r=>/=; first by rewrite ltEnat /= ltn_subRL.
    by rewrite leEnat leq_subRL.
  case: (m + n < j ?<= if ~~ r); rewrite ?andbF // !andbT.
  case: (ltnP i m)=>/= Hi.
  - by symmetry; apply/lteifS/ltn_addr.
  case: l=>/=; last by rewrite ltEnat /= ltn_subLR.
  by rewrite leEnat leq_subLR.
- case: (ltnP i m)=>/= Hi.
  - by symmetry; apply/lteifS/ltn_addr.
  case: l=>/=; last by rewrite ltEnat /= ltn_subLR.
  by rewrite leEnat leq_subLR.
case: (ltnP j m)=>/= Hj.
- symmetry; apply/negbTE; rewrite lteifNE negbK.
  by apply/lteifS/ltn_addr.
case: r=>/=; first by rewrite ltEnat /= ltn_subRL.
by rewrite leEnat leq_subRL.
Qed.

(* generalize to orderType? *)
Lemma mem_itv_inf (n : nat) : n \in `]-oo,+oo[.
Proof. by rewrite in_itv. Qed.

Section Lemmas.
Variable (A : Type).
Implicit Type (s : seq A).

Lemma slice_decompose s l r x y :
        &:s (Interval (BSide l x) (BSide r y)) =
        &:(&:s (Interval -oo (BSide r y))) (Interval (BSide l x) +oo).
Proof. by rewrite /slice /= drop0 take_size. Qed.

(* "test" lemmas *)
Lemma slice_ouou s a b :
        &:s `]a,b[ = &:(&:s `]-oo,b[) `]a,+oo[.
Proof. by rewrite slice_decompose. Qed.

(* TODO generalize? *)
Lemma slice_uouo s a b :
        &:s `]a,b+a] = &:(&:s `]a,+oo[) `]-oo,b[.
Proof.
by rewrite /slice /= !addn1 !addn0 drop0 take_size take_drop addnS.
Qed.

(* ... *)

(* some simplifying equalities on slices *)

Lemma slice_0L s y : &:s (Interval -oo y) = &:s (Interval (BLeft 0%N) y).
Proof. by rewrite /slice /= addn0. Qed.

Lemma slice_FR s x : &:s (Interval x +oo) = &:s (Interval x (BLeft (size s))).
Proof. by rewrite /slice /= addn0. Qed.

Lemma slice_uu s : &:s `]-oo, +oo[ = s.
Proof. by rewrite /slice /= drop0 take_size. Qed.

Lemma itv_underL s (i j : itv_bound nat) :
        bnd i (size s) = 0%N ->
        &:s (Interval i j) = &:s (Interval -oo j).
Proof. by move=>Hi; rewrite /slice /= Hi drop0. Qed.

Lemma itv_underR s (i j : itv_bound nat) :
        bnd j (size s) = 0%N ->
        &:s (Interval i j) = [::].
Proof. by move=>Hj; rewrite /slice /= Hj take0. Qed.

Corollary itv_under0R s (i : itv_bound nat) :
            &:s (Interval i (BLeft 0%N)) = [::].
Proof. by apply: itv_underR. Qed.

Lemma itv_overL s (i j : itv_bound nat) :
        size s <= bnd i (size s) ->
        &:s (Interval i j) = [::].
Proof.
move=>Hi /=; rewrite /slice /=; apply: drop_oversize.
rewrite size_take; case: ifP=>// H.
by apply/ltnW/(leq_trans H).
Qed.

Lemma itv_overR s (i j : itv_bound nat) :
        size s <= bnd j (size s) ->
        &:s (Interval i j) = &:s (Interval i +oo).
Proof. by move=>Hj; rewrite /slice /= take_size take_oversize. Qed.

Lemma itv_minfR s (i : itv_bound nat) :
        &:s (Interval i -oo) = [::].
Proof. by rewrite /slice /= take0. Qed.

Lemma itv_pinfL s (j : itv_bound nat) :
        &:s (Interval +oo j) = [::].
Proof.
rewrite /slice /=; apply: drop_oversize.
by rewrite size_take_min; apply: geq_minr.
Qed.

(* TODO unify the next two? *)
Lemma itv_swapped_bnd s (i j : itv_bound nat) :
        j <= i ->
        &:s (Interval i j) = [::].
Proof.
move=>H; rewrite /slice; apply: drop_oversize.
move: H; case: i=>[ib ix|[]]; case: j=>[jb jx|[]] //=;
rewrite ?bnd_simp ?take_size ?take0 ?drop_size //= size_take_min.
- rewrite leBSide; case: ib=>/=; case: jb=>/=; rewrite ?addn0 ?addn1=>Hji.
  - apply/leq_trans/Hji; exact: geq_minl.
  - apply/leq_trans/Hji; exact: geq_minl.
  - apply: leq_trans; first by exact: geq_minl.
    by apply: ltnW.
  by apply: leq_trans; first by exact: geq_minl.
by move=>_; exact: geq_minr.
Qed.

Lemma itv_swapped s (i j : itv_bound nat) :
        bnd j (size s) <= bnd i (size s) ->
        &:s (Interval i j) = [::].
Proof.
move=>H; rewrite /slice; apply: drop_oversize.
rewrite size_take_min; apply/leq_trans/H.
by exact: geq_minl.
Qed.

Corollary slice_usize s : s = &:s `]-oo, size s[.
Proof. by rewrite itv_overR /=; [rewrite slice_uu | rewrite addn0]. Qed.

(* slice size *)

Lemma slice_size s (i : interval nat) :
        size (&:s i) = minn (bnd i.2 (size s)) (size s) - bnd i.1 (size s).
Proof.
rewrite /slice; case: i=>[[l i|[]][r j|[]]] //=; rewrite ?take0 ?drop0 ?take_size ?drop_size ?minnn ?min0n ?subn0 //=.
- by rewrite size_drop size_take_min.
- by rewrite size_drop.
- by rewrite size_take_min.
- by rewrite size_drop size_take_min.
by rewrite subnn.
Qed.

(* splitting slice *)

Lemma slice_split_bnd s (i : interval nat) (x : itv_bound nat) :
        i.1 <= x <= i.2 ->
        &:s i = &:s (Interval i.1 x) ++ &:s (Interval x i.2).
Proof.
case: i=>i1 i2 /=.
case: x=>[b x|[]]; rewrite ?bnd_simp /=; first last.
- by move/eqP=>->; rewrite itv_pinfL cats0.
- by rewrite andbT =>/eqP->; rewrite itv_minfR.
case/boolP: (size s <= bnd (BSide b x) (size s)).
- move=>H Hx; rewrite (itv_overL _ H) cats0 (itv_overR _ H).
  apply: itv_overR; rewrite /= in H.
  case/andP: Hx=>_.
  case: i2=>[[] i2|[]] //= Hx; apply: (leq_trans H); case: {H}b Hx; rewrite bnd_simp ?addn0 ?addn1 //.
  by move=>Hx; apply/ltnW.
rewrite -ltNge ltEnat /= =>/ltnW/minn_idPl Hx.
case: i1=>[l i|[]]; case: i2=>[r j|[]] //=;
rewrite ?bnd_simp ?andbF ?andbT // ?lteBSide /slice /= ?drop0 ?take_size.
- case/andP=>Hi Hj.
  have Hxj : (x + ~~ b <= j + ~~r)%N.
  - case: r Hj=>/=; rewrite ?leEnat ?ltEnat; case: {Hx Hi}b=>/=;
    rewrite ?addn0 ?addn1 // => Hj;
    by apply: ltnW.
  have Hxi : (i + ~~ l <= x + ~~ b)%N.
  - case: l Hi=>/=; rewrite ?implybT ?implybF /= ?addn0 ?addn1 /= => Hi.
    - by apply/(leq_trans Hi)/leq_addr.
    by case: {Hx Hj Hxj}b Hi=>/=; rewrite ?leEnat ?ltEnat /= ?addn0 ?addn1.
  rewrite -{1}(subnKC Hxj) takeD drop_cat size_take_min Hx take_drop subnK //.
  rewrite ltn_neqAle Hxi andbT; case: eqP=>//= ->.
  by rewrite subnn drop0 drop_take_id.
- move=>Hi; rewrite -{1}(cat_take_drop (x + ~~ b) s) drop_cat size_take_min Hx.
  have Hxi : (i + ~~ l <= x + ~~ b)%N.
  - case: l Hi=>/=; rewrite ?implybT ?implybF /= ?addn0 ?addn1 /= => Hi.
    - by apply/(leq_trans Hi)/leq_addr.
    by case: {Hx}b Hi=>/=; rewrite ?leEnat ?ltEnat /= ?addn0 ?addn1.
  rewrite ltn_neqAle Hxi andbT; case: eqP=>//= ->.
  by rewrite subnn drop0 drop_take_id.
- move=>Hj.
  have Hbj : (x + ~~ b <= j + ~~ r)%N.
  - case: r Hj=>/=; rewrite ?leEnat ?ltEnat; case: {Hx}b=>/=;
    rewrite ?addn0 ?addn1 // => Hx;
    by apply: ltnW.
  by rewrite -{1}(subnKC Hbj) takeD take_drop subnK.
by move=>_; rewrite cat_take_drop.
Qed.

Corollary slice_split s (i : interval nat) b (x : nat) :
            x \in i ->
            &:s i = &:s (Interval i.1 (BSide b x)) ++ &:s (Interval (BSide b x) i.2).
Proof.
move=>Hx; apply: slice_split_bnd.
case: i Hx=>[[l i|[]][r j|[]]] //=;
rewrite in_itv /= ?andbT ?andbF // ?leBSide; case: b=>/=;
rewrite ?implybF ?implybT //=.
- by case/andP=>->/= /lteifW.
- by case/andP=>/lteifW->.
- by move/lteifW.
by move/lteifW.
Qed.

(* splitting whole list *)

Corollary slice_split_full s b (x : nat) :
            s = &:s (Interval -oo (BSide b x)) ++ &:s (Interval (BSide b x) +oo).
Proof. by rewrite -[LHS](slice_uu s); apply: slice_split. Qed.

(* slice extrusion *)

Lemma slice_extrude s (i : interval nat) :
        i.1 < i.2 ->
        s = &:s (Interval -oo i.1) ++ &:s i ++ &:s (Interval i.2 +oo).
Proof.
case: i=>[[[] i|[]][[] j|[]]] //=; rewrite bnd_simp=>H;
  rewrite ?itv_minfR ?itv_pinfL /= ?cats0.
- by rewrite -{1}(slice_uu s) (slice_split _ true (x:=i)) //=
    (slice_split _ true (x:=j) (i:=`[i, +oo[)) //= in_itv /= andbT; apply/ltnW.
- by rewrite -{1}(slice_uu s) (slice_split _ true (x:=i)) //=
    (slice_split _ false (x:=j) (i:=`[i, +oo[)) //= in_itv /= andbT.
- by rewrite -{1}(slice_uu s) (slice_split _ true (x:=i)).
- by rewrite -{1}(slice_uu s) (slice_split _ false (x:=i)) //=
    (slice_split _ true (x:=j) (i:=`]i, +oo[)) //= in_itv /= andbT.
- by rewrite -{1}(slice_uu s) (slice_split _ false (x:=i)) //=
    (slice_split _ false (x:=j) (i:=`]i, +oo[)) //= in_itv /= andbT.
- by rewrite -{1}(slice_uu s) (slice_split _ false (x:=i)).
- by rewrite -{1}(slice_uu s) (slice_split _ true (x:=j)).
- by rewrite -{1}(slice_uu s) (slice_split _ false (x:=j)).
by rewrite slice_uu.
Qed.

(* "test" lemmas *)
Corollary slice_uxou s i : s = &:s `]-oo, i] ++ &:s `]i, +oo[.
Proof. by rewrite -(slice_split _ _ (i:=`]-oo, +oo[)) // slice_uu. Qed.

Corollary slice_uoxu s i : s = &:s `]-oo, i[ ++ &:s `[i, +oo[.
Proof. by rewrite -(slice_split _ _ (i:=`]-oo, +oo[)) // slice_uu. Qed.

Corollary slice_uxxo s a b :
            a <= b ->
            &:s `]-oo, b] = &:s `]-oo, a] ++ &:s `]a, b].
Proof. by move=>Hab; rewrite (slice_split _ false (x:=a)). Qed.

Corollary slice_uxox s a b :
            a <= b ->
            &:s `]-oo, b] = &:s `]-oo, a[ ++ &:s `[a, b].
Proof. by move=>Hab; rewrite (slice_split _ true (x:=a)). Qed.

Corollary slice_uoox (s : seq A) a b :
            a < b ->
            &:s `]-oo, b[ = &:s `]-oo, a[ ++ &:s `[a, b[.
Proof. by move=>Hab; rewrite (slice_split _ true (x:=a)). Qed.

(* ... *)

(* singleton slice *)

Lemma slice_kk s k l r :
        &:s (Interval (BSide l k) (BSide r k)) =
        if l && ~~ r then oapp (cons^~ [::]) [::] (onth s k) else [::].
Proof.
rewrite /slice /=; case: (onth_sizeP s k)=>[|v] H; rewrite H /=.
- move/size_onthPn: H=>H; rewrite if_same.
  apply: drop_oversize; rewrite size_take ltnNge.
  have ->/= : (size s <= k + ~~ r)%N by apply/leq_trans/leq_addr.
  by apply/leq_trans/leq_addr.
move: (onth_size H)=>Hk; case: l; case: r=>/=;
rewrite ?addn0 ?addn1.
- by apply: drop_oversize; rewrite size_take Hk.
- rewrite -addn1 addnC -take_drop.
  rewrite (take_nth v); last by rewrite size_drop subn_gt0.
  by rewrite take0 /= nth_drop addn0 nth_onth H.
- by apply: drop_oversize; rewrite size_take Hk.
apply: drop_oversize; rewrite size_take; case: ifP=>// /negbT.
by rewrite -leqNgt.
Qed.

(* "test" lemmas *)
Corollary slice_kkxx s k :
            &:s `[k, k] = oapp (cons^~ [::]) [::] (onth s k).
Proof. by rewrite slice_kk. Qed.

Corollary slice_kkxo s k : &:s `[k,k[ = [::].
Proof. by rewrite slice_kk. Qed.

Corollary slice_kkox s k : &:s `]k,k] = [::].
Proof. by rewrite slice_kk. Qed.

Corollary slice_kkoo s k : &:s `]k,k[ = [::].
Proof. by rewrite slice_kk. Qed.

(* endpoint +1 *)

Lemma slice_oSL x a s :
        &:s (Interval (BLeft x.+1) a) = &:s (Interval (BRight x) a).
Proof.
case/boolP: (x.+1 \in Interval (BRight x) a)=>[H|].
- rewrite [RHS](slice_split _ true (x:=x.+1)) //=.
  suff ->: &:s `]x, x.+1[ = [::] by rewrite cat0s.
  by rewrite /slice /= addn0 addn1 drop_take_id.
rewrite in_itv /= negb_and ltEnat /= ltnS leqnn /=.
case: a=>[[] a|[]] //=.
- by rewrite -leNgt leEnat => H; rewrite !itv_swapped //= !addn0 ?addn1 leEnat.
- by rewrite -ltNge ltEnat /= => H; rewrite !itv_swapped //= !addn1 ?addn0 leEnat ltnS.
by move=>_; rewrite !itv_minfR.
Qed.

Lemma slice_oSR a x s :
        &:s (Interval a (BLeft x.+1)) = &:s (Interval a (BRight x)).
Proof.
case/boolP: (x \in Interval a (BLeft x.+1))=>[H|].
- rewrite (slice_split _ false (x:=x)) //=.
  suff ->: &:s `]x, x.+1[ = [::] by rewrite cats0.
  by rewrite /slice /= addn0 addn1 drop_take_id.
rewrite in_itv /= negb_and ltEnat /= ltnS leqnn /= orbF.
case: a=>[[] a|[]] //=.
- by rewrite -ltNge ltEnat /= => H; rewrite !itv_swapped //= !addn0 ?addn1 leEnat.
- by rewrite -leNgt leEnat => H; rewrite !itv_swapped //= !addn1 ?addn0 leEnat ltnS.
by move=>_; rewrite !itv_pinfL.
Qed.

(* endpoint -1 *)

Corollary slice_oPL a x s :
            &:s (Interval (BRight x.-1) a) = if 0 < x
                                               then &:s (Interval (BLeft x) a)
                                               else &:s (Interval (BRight x) a).
Proof. by case: x=>//= n; rewrite slice_oSL. Qed.

Corollary slice_oPR a x s :
            &:s (Interval a (BRight x.-1)) = if 0 < x
                                               then &:s (Interval a (BLeft x))
                                               else &:s (Interval a (BRight x)).
Proof. by case: x=>//= n; rewrite slice_oSR. Qed.

(* endpoint split *)

Lemma slice_xR a x s :
        a <= BLeft x ->
        &:s (Interval a (BRight x)) =
        oapp (rcons (&:s (Interval a (BLeft x))))
                    (&:s (Interval a +oo))
             (onth s x).
Proof.
move=>Hax; rewrite (slice_split _ true (x:=x)) /=; last first.
- rewrite in_itv /= lexx andbT.
  by case: a Hax=>/=[ax av|ax]; case: ax.
rewrite slice_kk /=; case: (onth_sizeP s x)=>[|v] H;
  rewrite H /=; last by rewrite cats1.
rewrite cats0 itv_overR //= addn0.
by apply/size_onthPn.
Qed.

Lemma slice_xL b x s :
        BRight x <= b ->
        &:s (Interval (BLeft x) b) =
        oapp (cons^~ (&:s (Interval (BRight x) b)))
                     [::]
             (onth s x).
Proof.
move=>Hxb; rewrite (slice_split _ false (x:=x)) /=; last first.
- rewrite in_itv /= lexx /=.
  by case: b Hxb=>/=[bx bv|bx]; case: bx.
rewrite slice_kk /=; case: (onth_sizeP s x)=>[|v] H; rewrite H //=.
rewrite itv_overL //= addn1; apply: ltW.
by apply/size_onthPn.
Qed.

(* slice of empty list *)

Lemma slice0 i :
        &:([::] : seq A) i = [::].
Proof.
by rewrite /slice /=; case: i=>[[[] av|[]]]; case=>[[] bv|[]].
Qed.

(* slice of one-element list *)

Lemma slice1 (k : A) i :
        &:[::k] i = if 0%N \in i then [::k] else [::].
Proof.
rewrite /slice in_itv /=.
case: i=>[[[] i|[]][[] j|[]]] //=;
rewrite ?drop0 ?addn0 ?addn1 ?andbF ?andbT //=.
- case: j=>[|j]/=; first by rewrite ltxx andbF.
  by rewrite andbT; case: i.
- by case: i.
- by case: i.
- by apply: drop_oversize; rewrite size_take /=; case: ifP=>//; case: j.
- by case: j.
by case: j.
Qed.

(* slice and constructors *)

Lemma slice_cat s1 s2 i :
        &:(s1++s2) i = &:s1 i ++ &:s2 (shl_itv i (size s1)).
Proof.
rewrite /slice; case: i=>[[l i|[]][r j|[]]] /=;
rewrite ?take0 ?drop0 ?take_size ?drop_size // ?size_cat.
- rewrite take_cat; case: ltnP=>Hj.
  - have ->/=: (j < size s1)%N by apply/leq_ltn_trans/Hj/leq_addr.
    by rewrite take0 /= cats0.
  rewrite (take_oversize (s:=s1)) //.
  move: Hj; rewrite leq_eqVlt; case/orP=>[/eqP Ej|Hj].
  - rewrite -Ej subnn take0 cats0 /=.
    case: r Ej=>/=.
    - by rewrite addn0=>->; rewrite ltnn subnn /= take0 /= cats0.
    by rewrite addn1=>->; rewrite !ltnS leqnn /= take0 /= cats0.
  rewrite (ltnNge j); have H1: (size s1 <= j)%N.
  - by case: r Hj=>/=; rewrite ?addn1 // addn0 => /ltnW.
  rewrite H1 drop_cat; case: ltnP=>Hi /=.
  - have ->/=: (i < size s1)%N by apply/leq_ltn_trans/Hi/leq_addr.
    by rewrite drop0 addnBAC.
  rewrite (drop_oversize (s:=s1)) //=.
  move: Hi; rewrite leq_eqVlt; case/orP=>[/eqP Ei|Hi].
  - rewrite -Ei subnn drop0 /=.
    case: l Ei=>/=.
    - by rewrite addn0=><-; rewrite ltnn subnn /= drop0 addnBAC.
    by rewrite addn1=><-; rewrite leqnn /= drop0 addnBAC.
  rewrite (ltnNge i); have H2: (size s1 <= i)%N.
  - by case: l Hi=>/=; rewrite ?addn1 // addn0 => /ltnW.
  by rewrite H2 /= !addnBAC.
- rewrite drop_cat; case: ltnP=>Hi /=.
  - have ->/=: (i < size s1)%N by apply/leq_ltn_trans/Hi/leq_addr.
    by rewrite drop0.
  rewrite (drop_oversize (s:=s1)) //=.
  move: Hi; rewrite leq_eqVlt; case/orP=>[/eqP Ei|Hi].
  - rewrite -Ei subnn drop0 /=.
    case: l Ei=>/=.
    - by rewrite addn0=><-; rewrite ltnn subnn /= drop0.
    by rewrite addn1=><-; rewrite leqnn /= drop0.
  rewrite (ltnNge i); have H2: (size s1 <= i)%N.
  - by case: l Hi=>/=; rewrite ?addn1 // addn0 => /ltnW.
  by rewrite H2 /= addnBAC.
- rewrite take_cat; case: ltnP=>Hj.
  - have ->/=: (j < size s1)%N by apply/leq_ltn_trans/Hj/leq_addr.
    by rewrite take0 /= cats0.
  rewrite (take_oversize (s:=s1)) //.
  move: Hj; rewrite leq_eqVlt; case/orP=>[/eqP Ej|Hj].
  - rewrite -Ej subnn take0 cats0 /=.
    case: r Ej=>/=.
    - by rewrite addn0=>->; rewrite ltnn subnn /= take0 /= cats0.
    by rewrite addn1=>->; rewrite !ltnS leqnn /= take0 /= cats0.
  rewrite (ltnNge j); have H1: (size s1 <= j)%N.
  - by case: r Hj=>/=; rewrite ?addn1 // addn0 => /ltnW.
  by rewrite H1 /= addnBAC.
by rewrite !drop_oversize //= size_take_min ?size_cat; apply: geq_minr.
Qed.

Lemma slice_cat_piecewise s1 s2 i :
        &:(s1++s2) i = if size s1 \in i
                        then &:s1 (Interval i.1 +oo) ++ &:s2 (Interval -oo (shl_bnd i.2 (size s1)))
                        else if bnd i.2 (size s1 + size s2) <= size s1
                               then &:s1 i
                               else &:s2 (shl_itv i (size s1)).
Proof.
rewrite slice_cat; case: i=>i j /=; case: ifP.
- rewrite in_itv; case/andP=>Hi Hj.
  rewrite (itv_overR _ (j:=j)); last first.
  - case: j Hj=>[[] j|[]] //=.
    - by rewrite addn0; move/ltnW.
    by rewrite addn1 leEnat; move/(ltnW (n:=j.+1)).
  rewrite (itv_underL (i:=shl_bnd i _)) //.
  case: i Hi=>[[] i|[]] //=; last by rewrite ltEnat /=; move=>->.
  rewrite leEnat leq_eqVlt; case/orP=>[/eqP->|->] //=.
  by rewrite ltnn /= subnn.
rewrite in_itv=>/negbT; rewrite negb_and=>H.
case: ifP=>Hj.
- rewrite (itv_underR (s:=s2)); first by rewrite cats0.
  case: {H}j Hj=>[[] j|[]] //=.
  - rewrite addn0 leEnat leq_eqVlt; case/orP=>[/eqP->|->] //=.
    by rewrite ltnn /= subnn.
  - by rewrite addn1 leEnat =>->.
  by rewrite leEnat -{2}(addn0 (size s1)) leq_add2l leqn0 => /eqP.
case/orP: H; last first.
- case: j Hj=>[[] j|[]] //=.
  - by rewrite addn0 -leNgt=>->.
  by rewrite leEnat addn1 -ltnNge =>->.
case: i=>[[] i|[]] //=; last by rewrite !itv_pinfL.
- rewrite leEnat -ltnNge => Hi.
  rewrite (ltnNge i) (ltnW Hi) /= itv_overL //= addn0 leEnat.
  by apply: ltnW.
rewrite ltEnat /= -leqNgt => Hi.
rewrite ltnNge Hi /= itv_overL //= addn1 leEnat.
by apply: ltnW.
Qed.

Lemma slice_cons x s i :
        &:(x::s) i = if 0%N \in i then x::&:s (shl_itv i 1) else &:s (shl_itv i 1).
Proof. by rewrite -cat1s slice_cat /= slice1; case: ifP. Qed.

Lemma slice_rcons x s i :
        &:(rcons s x) i = if size s \in i then rcons (&:s i) x else &:s i.
Proof.
rewrite -cats1 slice_cat slice1 mem_shl addn0.
by case: ifP=>_; [rewrite cats1 | rewrite cats0].
Qed.

(* mask *)

Lemma slice_mask s i :
        &:s i = let x := bnd i.1 (size s) in
                let y := bnd i.2 (size s) in
                mask (nseq x false ++ nseq (y-x) true) s.
Proof. by rewrite /slice /=; case: i=>i j /=; rewrite drop_take_mask. Qed.

(* count *)

Lemma slice_count p s i :
        count p (&:s i) =
        count (fun j => j \in i) (findall p s).
Proof.
elim: s i=>/= [|x s IH] i; first by rewrite slice0.
rewrite findall_cons slice_cons.
case/boolP: (p x)=>/= Hpx; case/boolP: (0 \in i)=>I0 /=.
- rewrite Hpx !add1n; congr S.
  rewrite IH count_map; apply: eq_count=>z /=.
  by rewrite mem_shl add1n.
- rewrite IH /= count_map; apply: eq_count=>z /=.
  by rewrite mem_shl add1n.
- rewrite (negbTE Hpx) /= IH /= count_map; apply: eq_count=>z /=.
  by rewrite mem_shl add1n.
rewrite IH /= count_map; apply: eq_count=>z /=.
by rewrite mem_shl add1n.
Qed.

(* has *)

Corollary slice_has p s i :
            has p (&:s i) =
            has (fun j => j \in i) (findall p s).
Proof. by rewrite !has_count slice_count. Qed.

End Lemmas.

(* map *)

Lemma slice_map {A B} (f : A -> B) i s :
        [seq f x | x <- &:s i] = &: [seq f x | x <- s] i.
Proof. by rewrite !slice_mask /= map_mask /= size_map. Qed.

Section LemmasEq.
Variable (A : eqType).
Implicit Type (s : seq A).

(* membership *)

Corollary slice_memE x s i :
            x \in &:s i =
            has (fun j => j \in i) (indexall x s).
Proof. by rewrite /indexall -has_pred1; apply: slice_has. Qed.

Corollary slice_memE1 x s i :
            (count_mem x s <= 1)%N ->
            x \in &:s i =
            (x \in s) && (bnd i.1 (size s) <= index x s < bnd i.2 (size s)).
Proof.
move=>H; rewrite slice_memE indexall_count1 //; case: ifP=>//= Hx; rewrite orbF.
by case: i=>/= [[[] i|[]][[] j|[]]]; rewrite in_itv /= ?ltEnat ?leEnat /=
     ?ltn0 ?addn0 ?addn1 ?andbT ?andbF // ?(leqNgt (size _)) index_mem Hx //= andbT.
Qed.

Corollary slice_uniq_memE x s i :
            uniq s ->
            x \in &:s i =
            (x \in s) && (bnd i.1 (size s) <= index x s < bnd i.2 (size s)).
Proof. by move=>U; apply: slice_memE1; rewrite (count_uniq_mem _ U) leq_b1. Qed.

(* subset *)

Lemma slice_subset s i1 i2 :
  i1 <= i2 ->
  {subset (&:s i1) <= &:s i2}.
Proof.
case: i1=>i1 j1; case: i2=>i2 j2.
rewrite subitvE; case/andP=>Hi Hj.
move=>x Hx.
have Hij : i1 <= j1.
- apply: contraLR Hx; rewrite -ltNge=>/ltW Hji.
  by rewrite itv_swapped_bnd.
rewrite (@slice_split_bnd _ _ _ i1) /=; last first.
- by rewrite Hi /=; apply/le_trans/Hj.
rewrite mem_cat; apply/orP; right.
rewrite (@slice_split_bnd _ _ _ j1) /=; last first.
- by rewrite Hj andbT.
by rewrite mem_cat Hx.
Qed.

Corollary slice_subset_full s i :
            {subset &:s i <= s}.
Proof.
by rewrite -{2}(slice_uu s); apply/slice_subset/itv_lex1.
Qed.

(* slicing preserves uniqueness *)

Lemma slice_uniq s i :
        uniq s -> uniq (&:s i).
Proof.
move=>U; rewrite /slice /=; case: i=>l u.
by apply/drop_uniq/take_uniq.
Qed.

(* slicing preserves sortedness *)

Lemma slice_sorted r s i :
        sorted r s -> sorted r (&:s i).
Proof.
move=>S; rewrite /slice /=; case: i=>l u.
by apply/drop_sorted/take_sorted.
Qed.

End LemmasEq.

(* slicing and rcons *)
Lemma codom_ux_rcons A n (f : {ffun 'I_n -> A}) (i : 'I_n) :
        &:(fgraph f) `]-oo, i : nat] = 
        rcons (&:(fgraph f) `]-oo, i : nat[) (f i).
Proof. by rewrite slice_xR // slice_uu onth_codom. Qed.




