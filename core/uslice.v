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
From pcm Require Import options prelude ordtype seqext slice useqord.
(* We assume the sequences are unique and use the first index,  *)
(* however most lemmas don't require this condition explicitly. *)
(* The ones that do are grouped in separate sections.           *)
Local Open Scope order_scope.
Import Order.Theory.

(* slicing by element index *)

Definition ix_bnd {A : eqType} (s : seq A) (i : itv_bound A) : itv_bound nat :=
  match i with
  | BSide  b x => BSide  b (index x s)
  | BInfty b   => BInfty _ b
  end.

Definition ix_itv {A : eqType} (s : seq A) (i : interval A) : interval nat :=
  let: Interval l u := i in
  Interval (ix_bnd s l) (ix_bnd s u).

Definition eq_slice {A : eqType} (s : seq A) (i : interval A) :=
  slice s (ix_itv s i).

Notation "&= s i" := (eq_slice s i)
 (at level 1, i at next level, s at next level,
  format "&= s  i") : fun_scope.

Section Lemmas.
Variable (A : eqType).
Implicit Type (s : seq A).

Lemma eqsl_uu s :
  &=s `]-oo,+oo[ = s.
Proof. by apply: slice_uu. Qed.

Lemma eqsl_underL s (i j : itv_bound A) :
  bnd (ix_bnd s i) (size s) = 0%N ->
  &=s (Interval i j) = &=s (Interval -oo j).
Proof. by move=>H; apply: itv_underL. Qed.

Lemma eqsl_underR s (i j : itv_bound A) :
  bnd (ix_bnd s j) (size s) = 0%N ->
  &=s (Interval i j) = [::].
Proof. by move=>H; apply: itv_underR. Qed.

Lemma eqsl_overL s (i j : itv_bound A) :
  size s <= bnd (ix_bnd s i) (size s) ->
  &=s (Interval i j) = [::].
Proof. by move=>H; apply: itv_overL. Qed.

Lemma eqsl_overR s (i j : itv_bound A) :
  size s <= bnd (ix_bnd s j) (size s) ->
  &=s (Interval i j) = &=s (Interval i +oo).
Proof. by move=>Hj; apply: itv_overR. Qed.

Lemma eqsl_swapped s (i j : itv_bound A) :
  bnd (ix_bnd s j) (size s) <= bnd (ix_bnd s i) (size s) ->
  &=s (Interval i j) = [::].
Proof.
by move=>H; rewrite /eq_slice /=; apply: itv_swapped.
Qed.

Corollary eqsl_notinL y b t s :
  t \notin s ->
  &=s (Interval (BSide b t) y) = [::].
Proof.
move=>T; apply: eqsl_overL=>/=.
by rewrite (memNindex T); apply: leq_addr.
Qed.

Corollary eqsl_notinR x b t s :
  t \notin s ->
  &=s (Interval x (BSide b t)) = &=s (Interval x +oo).
Proof.
move=>T; apply: eqsl_overR=>/=.
by rewrite (memNindex T); apply: leq_addr.
Qed.

Lemma eqsl_minfR s (i : itv_bound A) :
  &=s (Interval i -oo) = [::].
Proof. by rewrite /eq_slice /=; apply: itv_minfR. Qed.

Lemma eqsl_pinfL s (j : itv_bound A) :
  &=s (Interval +oo j) = [::].
Proof. by rewrite /eq_slice /=; apply: itv_pinfL. Qed.

Lemma eqsliceRO_notin s x a :
        x \notin &=s (Interval a (BLeft x)).
Proof.
rewrite /eq_slice /slice /= addn0.
apply/negP=>/mem_drop; apply/negP.
by apply: mem_take_index.
Qed.

Corollary eqslice_subset_full s i :
            {subset &=s i <= s}.
Proof. by exact: slice_subset_full. Qed.

(* splitting *)

Lemma eqslice_split (s : seq A) (i : interval A) b (x : A) :
        ix_bnd s i.1 <= BSide b (index x s) <= ix_bnd s i.2 ->
        &=s i = &=s (Interval i.1 (BSide b x)) ++ &=s (Interval (BSide b x) i.2).
Proof. by case: i=>i j H; rewrite /eq_slice; apply: slice_split_bnd. Qed.

Corollary eqslice_split_full s b (x : A) :
            s = &=s (Interval -oo (BSide b x)) ++ &=s (Interval (BSide b x) +oo).
Proof. by rewrite -[LHS](eqsl_uu s); apply: eqslice_split. Qed.

(* test lemmas / instantiations *)

Corollary eqsl_uoxx (ks : seq A) t1 t2 :
            t1 <=[ks] t2 ->
            &=ks `]-oo, t2] = &=ks `]-oo, t1[ ++ &=ks `[t1, t2].
Proof. by rewrite seqle_unlock=>H; apply: eqslice_split. Qed.

Corollary eqsl_uxoo (ks : seq A) t1 t2 :
            t1 <[ks] t2 ->
            &=ks `]-oo, t2[ = &=ks `]-oo, t1] ++ &=ks `]t1, t2[.
Proof. by rewrite seqlt_unlock=>H; apply: eqslice_split. Qed.

Corollary eqsl_uoxo (ks : seq A) t1 t2 :
            t1 <=[ks] t2 ->
            &=ks `]-oo, t2[ = &=ks `]-oo,t1[ ++ &=ks `[t1, t2[.
Proof. by rewrite seqle_unlock=>H; apply: eqslice_split. Qed.

Corollary eqsl_uxox (ks : seq A) t1 t2 :
            t1 <=[ks] t2 ->
            &=ks `]-oo, t2] = &=ks `]-oo, t1] ++ &=ks `]t1, t2].
Proof. by rewrite seqle_unlock=>H; apply: eqslice_split. Qed.

Corollary eqsl_xxou (ks : seq A) t1 t2 :
            t1 <=[ks] t2 ->
            &=ks `[t1, +oo[ = &=ks `[t1, t2] ++ &=ks `]t2, +oo[.
Proof. 
rewrite seqle_unlock=>H.
by apply: eqslice_split=>/=; rewrite andbT. 
Qed.

Corollary eqsl_uxou (ks : seq A) t : ks = &=ks `]-oo, t] ++ &=ks `]t, +oo[.
Proof. exact: eqslice_split_full. Qed.

Corollary eqsl_uoxu (ks : seq A) t : ks = &=ks `]-oo, t[ ++ &=ks `[t, +oo[.
Proof. exact: eqslice_split_full. Qed.

(*
Lemma eqsl_kk_out s l r k :
        ~~ l || r ->
        &=s (Interval (BSide l k) (BSide r k)) = [::].
Proof.
move=>H; apply: eqsl_swapped=>/=.
case/orP: H.
- by move/negbTE=>-> /=; case: r=>//=; rewrite addn1 addn0.
move=>-> /=; rewrite addn0; case: l=>/=; first by rewrite addn0.
by rewrite addn1.
Qed.
*)

Lemma eqsl_kk1 (s : seq A) l r k :
        &=s (Interval (BSide l k) (BSide r k)) =
        if [&& l, ~~ r & k \in s] then [:: k] else [::].
Proof.
rewrite /eq_slice /= slice_kk onth_index.
apply/esym; case: ifP; first by case/and3P=>->->->.
move/negbT; rewrite !negb_and negbK.
case/or3P=>[/negbTE->|->|/negbTE->] //=.
- by rewrite andbF.
by rewrite if_same.
Qed.

(* endpoint split of single-bounded interval *)

Lemma eqsl_uxR t s :
        &=s `]-oo, t] = if t \in s
                          then rcons (&=s `]-oo, t[) t
                          else &=s `]-oo, t[.
Proof.
rewrite /eq_slice /= (@slice_split _ _ _ true (index t s)) /=; last first.
- by rewrite in_itv /=.
rewrite slice_kk /= onth_index; case: ifP=>/= H.
- by rewrite cats1.
by rewrite cats0.
Qed.

Lemma eqsl_xuL t s :
        &=s `[t, +oo[ = if t \in s
                          then t :: &=s `]t, +oo[
                          else &=s `]t, +oo[.
Proof.
rewrite /eq_slice /= (@slice_split _ _ _ false (index t s)) //=; last first.
- by rewrite in_itv /= andbT.
by rewrite slice_kk /= onth_index; case: ifP.
Qed.

Lemma eqsl_xxL t1 t2 s :
        &=s `[t1, t2] = if (t1 <=[s] t2) && (t1 \in s)
                          then t1 :: &=s `]t1, t2]
                          else [::].
Proof.
rewrite /eq_slice seqle_unlock /=.
case: leqP=>I /=; last by rewrite itv_swapped_bnd.
rewrite (@slice_split _ _ _ false (index t1 s)) /=; last first.
- by rewrite in_itv /= lexx.
rewrite slice_kk /= onth_index; case: ifP=>//= /negbT N1.
by rewrite (memNindex N1) itv_overL //= addn1.
Qed.

Lemma eqsl_xxR t1 t2 s :
        &=s `[t1, t2] = if t1 <=[s] t2 then
                           if t2 \in s
                             then rcons (&=s `[t1, t2[) t2
                             else &=s `[t1, +oo[
                           else [::].
Proof.
rewrite /eq_slice seqle_unlock /=.
case: leqP=>I /=; last by rewrite itv_swapped_bnd //.
rewrite (@slice_split _ _ _ true (index t2 s)) /=; last first.
- by rewrite in_itv /= lexx andbT.
rewrite slice_kk /= onth_index /=; case: ifP=>/=; first by rewrite cats1.
rewrite cats0 => /negbT/memNindex->.
by apply: itv_overR=>/=; rewrite addn0.
Qed.

Lemma eqsl_xoL t1 t2 s :
        &=s `[t1, t2[ = if t1 <[s] t2
                          then t1 :: &=s `]t1, t2[
                          else [::].
Proof.
rewrite /eq_slice seqlt_unlock /=.
case: ltnP=>I; last by rewrite itv_swapped_bnd.
rewrite (@slice_split _ _ _ false (index t1 s)) /=; last first.
- by rewrite in_itv /= lexx.
rewrite slice_kk /= onth_index; case: ifP=>//= /negbT/memNindex E.
by move: I; rewrite E ltnNge index_size.
Qed.

Lemma eqsl_oxR t1 t2 s :
        &=s `]t1, t2] = if t1 <[s] t2 then
                          if t2 \in s
                            then rcons (&=s `]t1, t2[) t2
                            else &=s `]t1, +oo[
                          else [::].
Proof.
rewrite /eq_slice seqlt_unlock /=.
case: ltnP=>I; last by rewrite itv_swapped_bnd.
rewrite (@slice_split _ _ _ true (index t2 s)) /=; last first.
- by rewrite in_itv /= lexx andbT.
rewrite slice_kk /= onth_index /=; case: ifP=>/=; first by rewrite cats1.
rewrite cats0 =>/negbT/memNindex->.
by apply: itv_overR=>/=; rewrite addn0.
Qed.

(* some simplifying equalities on intervals *)

Lemma eqsl_uL_notinE s b t :
        t \notin s ->
        &=s `(Interval -oo (BSide b t)) = s.
Proof.
move=>N; rewrite /eq_slice /= itv_overR /=; first by exact: slice_uu.
by rewrite (memNindex N); exact: leq_addr.
Qed.

Lemma eqsl_uR_notinE s b t :
        t \notin s ->
        &=s `(Interval (BSide b t) +oo) = [::].
Proof.
move=>N; rewrite /eq_slice /= itv_overL //=.
by rewrite (memNindex N); exact: leq_addr.
Qed.

(* eqslice of nil *)
Lemma eqslice0 i :
        &=([::] : seq A) i = [::].
Proof. by rewrite /eq_slice slice0. Qed.

(* concat *)
(* TODO unify *)

Lemma eqsl_uL_catE s1 s2 b t :
        &= (s1 ++ s2) (Interval -oo (BSide b t)) =
        if t \in s1 then &= s1 (Interval -oo (BSide b t))
                    else s1 ++ &= s2 (Interval -oo (BSide b t)).
Proof.
rewrite /eq_slice slice_cat /= index_cat; case: ifP=>H1.
- by rewrite index_mem H1 itv_minfR cats0.
rewrite ltnNge leq_addr /= addnC addnK itv_overR /=; first by rewrite slice_uu.
by rewrite -addnA addnCA; exact: leq_addr.
Qed.

Lemma eqsl_uR_catE s1 s2 b t :
        &= (s1 ++ s2) (Interval (BSide b t) +oo) =
        if t \in s1 then &= s1 (Interval (BSide b t) +oo) ++ s2
                    else &= s2 (Interval (BSide b t) +oo).
Proof.
rewrite /eq_slice slice_cat /= index_cat; case: ifP=>H1.
- by rewrite index_mem H1 slice_uu.
rewrite ltnNge leq_addr /= addnC addnK itv_overL //=.
by rewrite -addnA addnCA; exact: leq_addr.
Qed.

Lemma eqsl_catE s1 s2 b1 t1 b2 t2 :
        &= (s1 ++ s2) (Interval (BSide b1 t1) (BSide b2 t2)) =
        if t1 \in s1
          then if t2 \in s1
                 then &= s1 (Interval (BSide b1 t1) (BSide b2 t2))
                 else &= s1 (Interval (BSide b1 t1) +oo) ++ &= s2 (Interval -oo (BSide b2 t2))
          else if t2 \in s1
                 then [::]
                 else &= s2 (Interval (BSide b1 t1) (BSide b2 t2)).
Proof.
rewrite /eq_slice slice_cat /= !index_cat.
case/boolP: (t1 \in s1)=>H1; case/boolP: (t2 \in s1)=>H2.
- by rewrite !index_mem H1 H2 itv_minfR cats0.
- rewrite index_mem H1 ltnNge leq_addr /= itv_overR /=; last by rewrite -addnA; exact: leq_addr.
  by congr (_ ++ _); rewrite addnC addnK.
- by rewrite ltnNge leq_addr /= index_mem H2 itv_minfR cats0 itv_overL //= -addnA; exact: leq_addr.
rewrite !ltnNge !leq_addr /= itv_overL /=; last by rewrite -addnA; exact: leq_addr.
by do 2!rewrite addnC addnK.
Qed.

(* cons lemmas *)
(* TODO unify *)

Lemma eqsl_uL_consE s b k t :
         &=(k :: s) (Interval -oo (BSide b t)) =
         if t == k then
           if b
             then [::]
             else [::k]
           else k :: &=s (Interval -oo (BSide b t)).
Proof.
rewrite -cat1s eqsl_uL_catE /= inE; case: eqVneq=>// {t}->.
by rewrite /eq_slice /= eqxx; case: b.
Qed.

Corollary eqsl_uL_consL s b t :
            &=(t :: s) (Interval -oo (BSide b t)) =
            if b then [::] else [::t].
Proof. by rewrite eqsl_uL_consE eqxx. Qed.

Lemma eqsl1_uL (k : A) b t :
        &=[::k] (Interval -oo (BSide b t)) =
        if ~~ b || (t!=k) then [::k] else [::].
Proof.
rewrite eqsl_uL_consE; case: eqVneq=>_.
- by rewrite orbF; case: b.
by rewrite orbT eqslice0.
Qed.

Lemma eqsl_uR_consE s b k t :
         &=(k :: s) (Interval (BSide b t) +oo) =
         if t == k then
           if b
             then k::s
             else s
           else &=s (Interval (BSide b t) +oo).
Proof.
rewrite -cat1s eqsl_uR_catE /= inE; case: eqVneq=>// {t}->.
by rewrite /eq_slice /= eqxx; case: b.
Qed.

Corollary eqsl_uR_consL s b t :
            &=(t :: s) (Interval (BSide b t) +oo) = if b then t::s else s.
Proof. by rewrite eqsl_uR_consE eqxx. Qed.

Lemma eqsl1_uR (k : A) b t :
        &=[::k] (Interval (BSide b t) +oo) =
        if b && (t==k) then [::k] else [::].
Proof.
rewrite eqsl_uR_consE; case: eqVneq=>_; first by rewrite andbT.
by rewrite eqslice0 andbF.
Qed.

Lemma eqsl_consE s k b1 t1 b2 t2 :
         &=(k :: s) (Interval (BSide b1 t1) (BSide b2 t2)) =
         if t1 == k then
           if t2 == k
             then if b1 && ~~ b2 then [::k] else [::]
             else if b1 then k :: &=s (Interval -oo (BSide b2 t2))
                        else &=s (Interval -oo (BSide b2 t2))
           else if t2 == k
                  then [::]
                  else &=s (Interval (BSide b1 t1) (BSide b2 t2)).
Proof.
rewrite -cat1s eqsl_catE /= !inE.
case: eqVneq=>[{t1}->|N1]; case: eqVneq=>[E2|N2] //=.
- by rewrite /eq_slice /= E2 eqxx; case: b1; case: b2.
by rewrite /eq_slice /= eqxx; case: b1.
Qed.

(* rcons lemmas *)

Lemma eqsl_uL_rconsE s b k t :
         &=(rcons s k) (Interval -oo (BSide b t)) =
         if t \in s
           then &=s (Interval -oo (BSide b t))
           else if ~~ b || (t!=k) then rcons s k else s.
Proof.
rewrite -cats1 eqsl_uL_catE /=; case: ifP=>//= _.
by rewrite eqsl1_uL; case: ifP=>_ //; rewrite cats0.
Qed.

Lemma eqsl_uR_rconsE s b k t :
         &=(rcons s k) (Interval (BSide b t) +oo) =
         if t \in s
           then rcons (&=s (Interval (BSide b t) +oo)) k
           else if b && (t == k) then [:: k] else [::].
Proof.
rewrite -cats1 eqsl_uR_catE /=; case: ifP=>//= _.
- by rewrite cats1.
by rewrite eqsl1_uR.
Qed.

Lemma eqsl_rconsE s k b1 t1 b2 t2 :
         &=(rcons s k) (Interval (BSide b1 t1) (BSide b2 t2)) =
         if t1 \in s then
           if t2 \in s
             then &=s (Interval (BSide b1 t1) (BSide b2 t2))
             else if b2 && (k==t2)
                    then &=s (Interval (BSide b1 t1) +oo)
                    else rcons (&=s (Interval (BSide b1 t1) +oo)) k
           else if t2 \in s
                  then [::]
                  else if [&& b1, k==t1 & (k==t2) ==> ~~b2]
                         then [::k] else [::].
Proof.
rewrite -cats1 eqsl_catE.
case/boolP: (t1 \in s)=>H1; case/boolP: (t2 \in s)=>H2 //.
- rewrite /eq_slice /=; case: eqVneq; case B2: b2=>/= _; try by rewrite cats1.
  by rewrite cats0.
by rewrite /eq_slice /=; case: eqVneq=>_; case: eqVneq=>_; case: b1; case: b2.
Qed.

(* test surgery lemmas *)

Lemma eqsl_uo_split t (s1 s2 : seq A) :
        t \notin s1 ->
        &=(s1++t::s2) `]-oo, t[ = s1.
Proof.
by move=>X1; rewrite eqsl_uL_catE (negbTE X1) eqsl_uL_consE eqxx cats0.
Qed.

Lemma eqsl_ou_split t (s1 s2 : seq A) :
        t \notin s1 ->
        &=(s1++t::s2) `]t, +oo[ = s2.
Proof.
by move=>X1; rewrite eqsl_uR_catE (negbTE X1) eqsl_uR_consE eqxx.
Qed.

Lemma eqsl_oo_split t1 t2 (s1 s2 s : seq A) :
        t1 != t2 ->
        t1 \notin s1 ->
        t2 \notin s1 ->
        t2 \notin s ->
        &=(s1++t1::s++t2::s2) `]t1, t2[ = s.
Proof.
move=>N X1 X21 X2.
rewrite eqsl_catE -cat_cons eqsl_uL_catE eqsl_catE /=
  eqsl_consE !eqsl_uL_consE eqsl_uR_consE /= !inE !eqxx /= !cats0.
by rewrite (negbTE X1) (negbTE X21) eq_sym (negbTE N) /= (negbTE X2).
Qed.

Corollary eqsl_oo_nil_split t1 t2 (s s2 : seq A) :
            t1 != t2 ->
            t2 \notin s ->
            &=(t1::s++t2::s2) `]t1, t2[ = s.
Proof.
move=>N X2.
by rewrite -(cat0s (_ :: _ ++ _)); apply: eqsl_oo_split.
Qed.

Corollary eqsl_oo_split_consec t1 t2 (s1 s2 : seq A) :
            t1 != t2 ->
            t1 \notin s1 -> t2 \notin s1 ->
            &=(s1++t1::t2::s2) `]t1, t2[ = [::].
Proof.
move=>N X1 X2.
by rewrite -(cat1s t1); apply: (@eqsl_oo_split _ _ _ _ [::]).
Qed.

Corollary eqsl_oo_nil_split_consec t1 t2 s :
            t1 != t2 ->
            &=(t1::t2::s) `]t1, t2[ = [::].
Proof.
move=>N.
by rewrite -(cat0s (_ :: _ :: _)); apply: eqsl_oo_split_consec.
Qed.

(* intervals and filter *)

(* TODO unify / better theory *)
Lemma eqsl_filterL (p : pred A) b (y : A) s :
        (y \notin s) || p y ->
        &= (filter p s) (Interval -oo (BSide b y)) = filter p (&= s (Interval -oo (BSide b y))).
Proof.
case/orP=>Hy.
- rewrite !eqsl_notinR //=; first by rewrite !eqsl_uu.
  by apply: contra Hy; rewrite mem_filter; case/andP.
elim: s=>//= h s IH.
case/boolP: (p h)=>/= Hp; last first.
- rewrite {}IH eqsl_uL_consE; case: eqVneq=>[E|_] /=.
  - by rewrite -E Hy in Hp.
  by rewrite (negbTE Hp).
rewrite !eqsl_uL_consE; case: eqVneq=>_ /=.
- by case: {IH}b=>//=; rewrite Hp.
by rewrite Hp IH.
Qed.

Lemma eqsl_filterR (p : pred A) b (x : A) s :
        (x \notin s) || p x ->
        &= (filter p s) (Interval (BSide b x) +oo) = filter p (&= s (Interval (BSide b x) +oo)).
Proof.
case/orP=>Hx.
- by rewrite !eqsl_notinL //= mem_filter negb_and Hx orbT.
elim: s=>//=h s IH.
case/boolP: (p h)=>/= Hp; last first.
- rewrite {}IH eqsl_uR_consE; case: eqVneq=>[E|_] //=.
  by rewrite -E Hx in Hp.
rewrite !eqsl_uR_consE; case: eqVneq=>//= _.
by case: {IH}b=>//=; rewrite Hp.
Qed.

Lemma eqsl_filter (p : pred A) b1 t1 b2 t2 s :
        (t1 \notin s) || (p t1 && ((t2 \notin s) || p t2)) ->
        &= (filter p s) (Interval (BSide b1 t1) (BSide b2 t2)) =
        filter p (&= s (Interval (BSide b1 t1) (BSide b2 t2))).
Proof.
case/orP=>[N1|/andP [H1]].
- by rewrite !eqsl_notinL //= mem_filter negb_and N1 orbT.
case/orP=>H2.
- rewrite !eqsl_notinR //=.
  - by rewrite eqsl_filterR // H1 orbT.
  by rewrite mem_filter negb_and H2 orbT.
elim: s=>//= h s IH.
case/boolP: (p h)=>/= Hp; last first.
- rewrite {}IH eqsl_consE; case: eqVneq=>[E1|_].
  - by rewrite -E1 H1 in Hp.
  case: eqVneq=>[E2|_] //.
  by rewrite -E2 H2 in Hp.
rewrite !eqsl_consE; case: eqVneq=>/=_; case: eqVneq=>//=_.
- by case: ifP=>//= _; rewrite Hp.
rewrite eqsl_filterL; last by rewrite H2 orbT.
by case: ifP=>//= _; rewrite Hp.
Qed.

Lemma eqslice_mem (i : interval A) (ks : seq A) (k : A) :
        k \in &=ks i =
        has (fun j => j \in ix_itv ks i) (indexall k ks).
Proof. by rewrite /eq_slice slice_memE. Qed.

Lemma eqslice_sorted r s i :
        sorted r s -> sorted r (&=s i).
Proof. by exact: slice_sorted. Qed.

End Lemmas.

Section LemmasUniq.
Variable (A : eqType).
Implicit Type (s : seq A).

Lemma eqsliceLO_notin (s : seq A) x b :
        uniq s ->
        x \notin &=s (Interval (BRight x) b).
Proof.
rewrite /eq_slice /slice /= addn1 => U.
move: (mem_drop_indexlast x s); rewrite indexlast_uniq //.
by apply/contra/prefix_drop_sub/prefix_take.
Qed.

Lemma eqsl_lastR_uniq s x :
        uniq s ->
        s = &=s `]-oo, (last x s)].
Proof.
move=>U; rewrite /eq_slice /= [LHS]slice_usize index_last_size_uniq // slice_oPR.
by case: ifP=>// /negbT; rewrite -ltnNge /= ltnS leqn0 => /eqP/size0nil->.
Qed.

Lemma eqslice_uniq s i :
        uniq s -> uniq (&=s i).
Proof.
rewrite /eq_slice; apply: slice_uniq.
Qed.

Lemma eqslice_mem_uniq (i : interval A) s (x : A) :
        uniq s ->
        x \in &=s i =
        (x \in s) && (index x s \in ix_itv s i).
Proof.
move=>U; rewrite eqslice_mem indexall_uniq //.
by case: ifP=>//= _; rewrite orbF.
Qed.

End LemmasUniq.

(* interaction of slicing and sequence ordering under uniqueness assumptions *)

Section SliceSeqOrd.
Variable (A : eqType).
Implicit Type (s : seq A).

(* TODO generalize / refactor to useq? *)
Lemma uniq_ux_filter s i :
        uniq s ->
        &=s `]-oo, i] = [seq x <- s | x <=[s] i].
Proof.
move=>U; rewrite /eq_slice /= /slice /= drop0 addn1.
elim: s U=>//=h s IH.
case/andP=>Nh U; rewrite sle_cons eqxx /=.
congr (cons _); case: (eqVneq i h)=>[E|N].
- rewrite -{h}E in Nh *; rewrite take0 -(filter_pred0 s).
  apply: eq_in_filter=>z Hz /=; rewrite sle_cons eqxx /= orbF.
  by apply/esym/negbTE; apply: contraNneq Nh=><-.
rewrite IH //; apply: eq_in_filter=>z Hz; rewrite sle_cons N /=.
suff: (z != h) by move/negbTE=>->.
by apply: contraNneq Nh=><-.
Qed.

Lemma uniq_uo_filter s i :
        uniq s ->
        &=s `]-oo, i[ = [seq x <- s | x <[s] i].
Proof.
move=>U; rewrite /eq_slice /= /slice /= drop0 addn0.
elim: s U=>//=h s IH.
case/andP=>Nh U; rewrite slt_cons eqxx /= andbT.
case: (eqVneq i h)=>[E|N] /=.
- rewrite -{h}E in Nh *; rewrite -(filter_pred0 s).
  by apply: eq_in_filter=>z Hz /=; rewrite slt_cons eqxx.
congr (cons _); rewrite IH //; apply: eq_in_filter=>z Hz.
rewrite slt_cons N /=.
suff: (z != h) by move/negbTE=>->.
by apply: contraNneq Nh=><-.
Qed.

(* sequence ordering, intervals, and last *)

Lemma olt_ole_last k s x t :
        uniq (k::s) -> t != k ->
        x <[k::s] t = x <=[k::s] (last k (&=s `]-oo, t[)).
Proof.
elim: s k=>/= [|y s IH] k //=.
- rewrite slt_cons slt_nil sle_cons sle_nil andbT eqxx orbF.
  by move=>_ ->.
rewrite inE negb_or -andbA; case/and4P=>Nky K Y U Nkt.
rewrite slt_cons sle_cons Nkt /=; case: (eqVneq x k)=>//= Nkx.
rewrite eqsl_uL_consE; case: (eqVneq t y)=>/= [E|Nty].
- by rewrite eqxx /= E sltR.
suff -> /= : last y (&=s `]-oo, t[) != k by rewrite IH //= Y.
apply: contraTneq (mem_last y (&=s `]-oo, t[))=> E.
rewrite inE E negb_or Nky /=; apply: contra K.
by exact: slice_subset_full.
Qed.

(* a slight variation to add the cons to last *)
Corollary olt_ole_last' k s x t :
            uniq (k::s) -> t != k ->
            x <[k::s] t = x <=[k::s] (last k (&=(k::s) `]-oo, t[)).
Proof. by move=>U K; rewrite olt_ole_last // eqsl_uL_consE (negbTE K). Qed.

Corollary eqsl_uox_last k s t :
            uniq (k::s) -> t != k ->
            &=(k :: s) `]-oo, last k (&=s `]-oo, t[) ] = &=(k :: s) `]-oo,t[.
Proof.
move=>U K.
rewrite (uniq_ux_filter _ U) (uniq_uo_filter _ U).
by apply: eq_in_filter=>x _; rewrite -olt_ole_last.
Qed.

(* membership *)

Lemma mem_oo t1 t2 (ks : seq A) (k : A) :
        uniq ks ->
        reflect ([/\ k \in ks, t1 <[ks] k & k <[ks] t2])
                (k \in &=ks `]t1, t2[).
Proof. 
rewrite !seqlt_unlock=>U.
by rewrite eqslice_mem_uniq // in_itv; apply: and3P. 
Qed.

Lemma mem_xo t1 t2 (ks : seq A) k :
        uniq ks ->
        reflect ([/\ k \in ks, t1 <=[ks] k & k <[ks] t2])
                (k \in &=ks `[t1, t2[).
Proof. 
rewrite seqlt_unlock seqle_unlock=>U.
by rewrite eqslice_mem_uniq // in_itv; apply: and3P. 
Qed.

Lemma mem_ox t1 t2 (ks : seq A) k :
        uniq ks ->
        reflect ([/\ k \in ks, t1 <[ks] k & k <=[ks] t2])
                (k \in &=ks `]t1, t2]).
Proof. 
rewrite seqlt_unlock seqle_unlock=>U.
by rewrite eqslice_mem_uniq // in_itv; apply: and3P. 
Qed.

Lemma mem_xx t1 t2 (ks : seq A) k :
        uniq ks ->
        reflect ([/\ k \in ks, t1 <=[ks] k & k <=[ks] t2])
                (k \in &=ks `[t1, t2]).
Proof. 
rewrite !seqle_unlock=>U.
by rewrite eqslice_mem_uniq // in_itv; apply: and3P. 
Qed.

Lemma mem_uo t (ks : seq A) k :
        uniq ks ->
        reflect ([/\ k \in ks & k <[ks] t])(k \in &=ks `]-oo, t[).
Proof. 
rewrite seqlt_unlock=>U.
by rewrite eqslice_mem_uniq // in_itv; apply: andP. 
Qed.

Lemma mem_ux t (ks : seq A) k :
        uniq ks ->
        reflect ([/\ k \in ks & k <=[ks] t])(k \in &=ks `]-oo, t]).
Proof. 
rewrite seqle_unlock=>U.
by rewrite eqslice_mem_uniq // in_itv; apply: andP. 
Qed.

Lemma mem_ou t (ks : seq A) k :
        uniq ks ->
        reflect ([/\ k \in ks & t <[ks] k])(k \in &=ks `]t, +oo[).
Proof. 
rewrite seqlt_unlock=>U.
by rewrite eqslice_mem_uniq // in_itv /= andbT; apply: andP. 
Qed.

Lemma mem_xu t (ks : seq A) k :
        uniq ks ->
        reflect ([/\ k \in ks & t <=[ks] k])(k \in &=ks `[t, +oo[).
Proof. 
rewrite seqle_unlock=>U.
by rewrite eqslice_mem_uniq // in_itv /= andbT; apply: andP. 
Qed.

(* has predT lemmas *)

Lemma has_predT_uslice (ks : seq A) i :
        uniq ks ->
        has predT (&=ks i) = has (fun z => index z ks \in ix_itv ks i) ks.
Proof.
move=>U; apply/hasP/hasP; case=>x.
- by rewrite eqslice_mem_uniq // =>/andP [Hx Hi] _; exists x.
by move=>Hx Hi; exists x=>//; rewrite eqslice_mem_uniq // Hx.
Qed.

(* corollaries *)
Lemma has_oo t1 t2 (ks : seq A) :
        uniq ks ->
        has predT (&=ks `]t1, t2[) = has (fun z => t1 <[ks] z && z <[ks] t2) ks.
Proof. 
move/has_predT_uslice=>->; apply: eq_has=>z. 
by rewrite !seqlt_unlock in_itv. 
Qed.

Lemma has_ox t1 t2 (ks : seq A) :
        uniq ks ->
        has predT (&=ks `]t1, t2]) = has (fun z => t1 <[ks] z && z <=[ks] t2) ks.
Proof. 
move/has_predT_uslice=>->; apply: eq_has=>z.
by rewrite seqlt_unlock seqle_unlock in_itv. 
Qed.

Lemma has_xo t1 t2 (ks : seq A) :
        uniq ks ->
        has predT (&=ks `[t1, t2[) = has (fun z => t1 <=[ks] z && z <[ks] t2) ks.
Proof. 
move/has_predT_uslice=>->; apply: eq_has=>z.
by rewrite seqle_unlock seqlt_unlock in_itv. 
Qed.

Lemma has_xx t1 t2 (ks : seq A) :
        uniq ks ->
        has predT (&=ks `[t1, t2]) = has (fun z => t1 <=[ks] z && z <=[ks] t2) ks.
Proof. 
move/has_predT_uslice=>->; apply: eq_has=>z.
by rewrite !seqle_unlock in_itv. 
Qed.

Lemma has_ou t (ks : seq A) :
        uniq ks ->
        has predT (&=ks `]t, +oo[) = has (fun z => t <[ks] z) ks.
Proof. 
move/has_predT_uslice=>->; apply: eq_has=>z.
by rewrite seqlt_unlock in_itv /= andbT. 
Qed.

Lemma has_xu t (ks : seq A) :
        uniq ks ->
        has predT (&=ks `[t, +oo[) = has (fun z => t <=[ks] z) ks.
Proof. 
move/has_predT_uslice=>->; apply: eq_has=>z.
by rewrite seqle_unlock in_itv /= andbT. 
Qed.

Lemma has_uo t (ks : seq A) :
        uniq ks ->
        has predT (&=ks `]-oo, t[) = has (fun z => z <[ks] t) ks.
Proof. 
move/has_predT_uslice=>->; apply: eq_has=>z.
by rewrite seqlt_unlock in_itv. 
Qed.

Lemma has_ux t (ks : seq A) :
        uniq ks ->
        has predT (&=ks `]-oo, t]) = has (fun z => z <=[ks] t) ks.
Proof. 
move/has_predT_uslice=>->; apply: eq_has=>z.
by rewrite seqle_unlock in_itv. 
Qed.

(* negation of has on the left side *)

Lemma hasNL_oo (ks : seq A) t1 t2 (p : pred A) :
        uniq ks -> t1 <[ks] t2 ->
        ~~ has p (&=ks `]t1, t2[) ->
        {in ks, forall z, p z -> z <[ks] t2 = z <=[ks] t1}.
Proof.
move=>U T /hasPn H z K P.
move: (H z); rewrite eqslice_mem_uniq // in_itv K /= =>/contraL/(_ P).
rewrite negb_and -!seqlt_unlockE -!sleNgt; case/orP=>Hz.
- by rewrite Hz; apply: (sle_slt_trans Hz).
rewrite sltNge Hz sleNgt; congr negb; apply/esym.
by apply: (slt_sle_trans T).
Qed.

Lemma hasNL_ox (ks : seq A) t1 t2 (p : pred A) :
        uniq ks -> t1 <=[ks] t2 ->
        ~~ has p (&=ks `]t1, t2]) ->
        {in ks, forall z, p z -> z <=[ks] t2 = z <=[ks] t1}.
Proof.
move=>U T /hasPn H z K P.
move: (H z); rewrite eqslice_mem_uniq // in_itv K /= =>/contraL/(_ P).
rewrite negb_and -seqlt_unlockE -seqle_unlockE -sleNgt -sltNge.
case/orP=>Hz.
- by rewrite Hz; apply: (sle_trans Hz).
rewrite !sleNgt Hz; congr negb; apply/esym.
by apply: (sle_slt_trans T).
Qed.

Lemma hasNL_xo (ks : seq A) t1 t2 (p : pred A) :
       uniq ks -> t1 <=[ks] t2 ->
       ~~ has p (&=ks `[t1, t2[) ->
       {in ks, forall z, p z -> z <[ks] t2 = z <[ks] t1}.
Proof.
move=>U T /hasPn H z K P.
move: (H z); rewrite eqslice_mem_uniq // in_itv K /= =>/contraL/(_ P).
rewrite negb_and -seqle_unlockE -seqlt_unlockE -sltNge -sleNgt.
case/orP=>Hz.
- by rewrite Hz; apply: (slt_sle_trans Hz).
rewrite !sltNge Hz; congr negb; apply/esym.
by apply: (sle_trans T).
Qed.

Lemma hasNL_xx (ks : seq A) t1 t2 (p : pred A) :
        uniq ks -> t1 <=[ks] t2 ->
        ~~ has p (&=ks `[t1, t2]) ->
        {in ks, forall z, p z -> z <=[ks] t2 = z <[ks] t1}.
Proof.
move=>U T /hasPn H z K P.
move: (H z); rewrite eqslice_mem_uniq // in_itv K /= =>/contraL/(_ P).
rewrite negb_and -!seqle_unlockE -!sltNge; case/orP=>Hz.
- by rewrite Hz; apply/sltW/(slt_sle_trans Hz).
rewrite sltNge sleNgt Hz; congr negb; apply/esym.
by apply/sltW/(sle_slt_trans T).
Qed.

Lemma hasNL_ou (ks : seq A) t (p : pred A) :
        uniq ks ->
        ~~ has p (&=ks `]t, +oo[) -> {in ks, forall z, p z -> z <=[ks] t}.
Proof.
move=>U /hasPn H z K P.
move: (H z); rewrite eqslice_mem_uniq // in_itv K /= andbT =>/contraL/(_ P).
by rewrite -seqlt_unlockE -sleNgt.
Qed.

Lemma hasNL_xu (ks : seq A) t (p : pred A) :
        uniq ks ->
        ~~ has p (&=ks `[t, +oo[) -> {in ks, forall z, p z -> z <[ks] t}.
Proof.
move=>U /hasPn H z K P.
move: (H z); rewrite eqslice_mem_uniq // in_itv K /= andbT =>/contraL/(_ P).
by rewrite -seqle_unlockE -sltNge.
Qed.

Lemma hasNL_uo (ks : seq A) t (p : pred A) :
        uniq ks ->
        ~~ has p (&=ks `]-oo, t[) -> {in ks, forall z, p z -> t <=[ks] z}.
Proof.
move=>U /hasPn H z K P.
move: (H z); rewrite eqslice_mem_uniq // in_itv K /= =>/contraL/(_ P).
by rewrite -seqlt_unlockE -sleNgt.
Qed.

Lemma hasNL_ux (ks : seq A) t (p : pred A) :
        uniq ks ->
        ~~ has p (&=ks `]-oo, t]) -> {in ks, forall z, p z -> t <[ks] z}.
Proof.
move=>U /hasPn H z K P.
move: (H z); rewrite eqslice_mem_uniq // in_itv K /= =>/contraL/(_ P).
by rewrite -seqle_unlockE -sltNge.
Qed.

(* negation of has on the right side *)

Lemma hasNR_oo (ks : seq A) t1 t2 (p : pred A) :
        uniq ks ->
        {in ks, forall z, p z -> z <[ks] t2 = z <=[ks] t1} ->
        ~~ has p (&=ks `]t1, t2[).
Proof.
move=>U T; apply/hasPn=>z; rewrite eqslice_mem_uniq // in_itv /=.
rewrite -!seqlt_unlockE; case/and3P=>H1 H2 H3; apply: contraL H2=>P. 
by rewrite -sleNgt -(T _ H1 P).
Qed.

Lemma hasNR_ox (ks : seq A) t1 t2 (p : pred A) :
        uniq ks ->
        {in ks, forall z, p z -> z <=[ks] t2 = z <=[ks] t1} ->
        ~~ has p (&=ks `]t1, t2]).
Proof.
move=>U T; apply/hasPn=>z; rewrite eqslice_mem_uniq // in_itv /=.
rewrite -seqlt_unlockE -seqle_unlockE.
case/and3P=>H1 H2 H3; apply: contraL H2=>P.
by rewrite -sleNgt -(T _ H1 P).
Qed.

Lemma hasNR_xo (ks : seq A) t1 t2 (p : pred A) :
        uniq ks ->
        {in ks, forall z, p z -> z <[ks] t2 = z <[ks] t1} ->
        ~~ has p (&=ks `[t1, t2[).
Proof.
move=>U T; apply/hasPn=>z; rewrite eqslice_mem_uniq // in_itv /=.
rewrite -seqlt_unlockE -seqle_unlockE.
case/and3P=>H1 H2 H3; apply: contraL H2=>P.
by rewrite -sltNge -(T _ H1 P).
Qed.

Lemma hasNR_xx (ks : seq A) t1 t2 (p : pred A) :
        uniq ks ->
        {in ks, forall z, p z -> z <=[ks] t2 = z <[ks] t1} ->
        ~~ has p (&=ks `[t1, t2]).
Proof.
move=>U T; apply/hasPn=>z; rewrite eqslice_mem_uniq // in_itv /=.
rewrite -!seqle_unlockE.
case/and3P=>H1 H2 H3; apply: contraL H2=>P.
by rewrite -sltNge -(T _ H1 P).
Qed.

Lemma hasNR_ou (ks : seq A) t (p : pred A) :
        uniq ks ->
        {in ks, forall z, p z -> z <=[ks] t} ->
        ~~ has p (&=ks `]t, +oo[).
Proof.
move=>U T; apply/hasPn=>z; rewrite eqslice_mem_uniq // in_itv /= andbT.
rewrite -seqlt_unlockE; case/andP=>H1 H2; apply: contraL H2=>P.
by rewrite -sleNgt; apply: T.
Qed.

Lemma hasNR_xu (ks : seq A) t (p : pred A) :
        uniq ks ->
        {in ks, forall z, p z -> z <[ks] t} ->
        ~~ has p (&=ks `[t, +oo[).
Proof.
move=>U T; apply/hasPn=>z; rewrite eqslice_mem_uniq // in_itv /= andbT.
rewrite -seqle_unlockE; case/andP=>H1 H2; apply: contraL H2=>P.
by rewrite -sltNge; apply: T.
Qed.

Lemma hasNR_uo (ks : seq A) t (p : pred A) :
        uniq ks ->
        {in ks, forall z, p z -> t <=[ks] z} ->
        ~~ has p (&=ks `]-oo, t[).
Proof.
move=>U T; apply/hasPn=>z; rewrite eqslice_mem_uniq // in_itv /=.
rewrite -seqlt_unlockE; case/andP=>H1 H2; apply: contraL H2=>P.
by rewrite -sleNgt; apply: T.
Qed.

Lemma hasNR_ux (ks : seq A) t (p : pred A) :
        uniq ks ->
        {in ks, forall z, p z -> t <[ks] z} ->
        ~~ has p (&=ks `]-oo, t]).
Proof.
move=>U T; apply/hasPn=>z; rewrite eqslice_mem_uniq // in_itv /=.
rewrite -seqle_unlockE; case/andP=>H1 H2; apply: contraL H2=>P.
by rewrite -sltNge; apply: T.
Qed.

End SliceSeqOrd.
