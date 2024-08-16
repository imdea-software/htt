(*
Copyright 2023 IMDEA Software Institute
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

From mathcomp Require Import ssreflect ssrbool ssrfun fintype.
From mathcomp Require Import eqtype ssrnat seq bigop choice.
From pcm Require Import options axioms pred seqext.
From pcm Require Import prelude pcm unionmap natmap heap autopcm automap.
From htt Require Import options model heapauto tree.

(**************)
(**************)
(* Union-find *)
(**************)
(**************)

(******************)
(* inverted trees *)
(******************)

(* the layout of a tree in the heap and the map of set reps of the tree *)
(* should lock to avoid exposing the folds upon simplification *)
(* as they make the lemmas unreadable *)
(* will provide the explicit big equations for rewriting *)

Fixpoint tlay (t : tree ptr) (r : ptr) : heap :=
  foldr (fun x h => h \+ tlay x (rt t)) (rt t :-> r) (ch t).

Fixpoint tset (t : tree ptr) (r : ptr) : umap ptr ptr :=
  foldr (fun t h => h \+ tset t r) (rt t \\-> r) (ch t).

(* explicit equations for expanding the defs of tlayout and tset *)
(* Ideally, these should have been the actual fixed point defs *)
(* but Coq can't see that such defs are well-founded *)

Lemma tlayE t r :
        tlay t r =
        rt t :-> r \+ \big[join/Unit]_(x <- ch t) (tlay x (rt t)).
Proof.
case: t=>a ts /=; rewrite foldr_join; congr (_ \+ _).
elim: ts=>[|t ts IH] /=; first by rewrite big_nil.
by rewrite big_cons IH joinC.
Qed.

Lemma tsetE t r :
        tset t r =
        rt t \\-> r \+ \big[join/Unit]_(x <- ch t) (tset x r).
Proof.
case: t=>a ts /=; rewrite foldr_join; congr (_ \+ _).
elim: ts=>[|t ts IH] /=; first by rewrite big_nil.
by rewrite big_cons IH joinC.
Qed.


(*******************)
(* dom/valid/range *)
(* inverted trees  *)
(*******************)

Lemma valid_dom_tset (t : tree ptr) r :
        (valid (tset t r) = uniq (preorder t)) *
        (dom (tset t r) =i
         if valid (tset t r) then preorder t else [::]).
Proof.
elim/tree_ind2: t r=>a ts IH r. rewrite tsetE preorderE.
rewrite validPtUn !big_valid_dom_seq /= big_cat_mem_has.
case: allP=>H /=; last first.
- split=>[|x]; last first.
  - by rewrite domUn inE validPtUn !big_valid_dom_seq; case: allP.
  rewrite andbC; case: uniq_big_catE=>//=; case=>H1 _ _.
  by case: H=>t T; rewrite IH // H1.
case U1: (uniq _)=>/=; last first.
- rewrite andbC; case U2: (uniq _)=>/=; last first.
  - by split=>// x; rewrite domPtUn inE validPtUn /= !big_valid_dom_seq U1 andbF.
  case/uniq_big_catE: U2=>H1 H2 H3.
  case: uniq_big_catE U1=>//; case; split.
  - by move=>i; rewrite uniq_dom.
  - move=>i k X D; apply: (H2 i k X).
    by rewrite (IH i X r) H in D.
  move=>i j k X Y Di Dj.
  apply: (H3 i j k)=>//; first by rewrite (IH i X r) H in Di.
  by rewrite (IH j Y r) H in Dj.
rewrite big_cat_mem_has andbC; case: uniq_big_catE=>/=; last first.
- case/uniq_big_catE: U1=>H1 H2 H3; case; split.
  - by move=>i X; rewrite -(IH i X r) H.
  - by move=>i k X D; apply: (H2 i k X); rewrite (IH i X r) H.
  move=>i j k X Y Di Dj; apply: (H3 i j k X Y); first by rewrite (IH i X r) H.
  by rewrite (IH j Y r) H.
case=>K1 K2 K3; split=>[|x].
- by rewrite -!all_predC; apply: eq_in_all=>i X; rewrite /= IH ?H.
rewrite domPtUn inE validPtUn /= !big_valid_dom_seq U1 andbT.
case: allP=>//= _; rewrite !big_cat_mem_has -all_predC.
case: allP=>//= A; rewrite inE big_cat_mem_has eq_sym.
by case: (x =P a)=>//= _; apply: eq_in_has=>i X; rewrite IH ?H.
Qed.

Lemma valid_tset (t : tree ptr) r :
        valid (tset t r) = uniq (preorder t).
Proof. by rewrite valid_dom_tset. Qed.

Lemma dom_tset_ord (t : tree ptr) r :
        dom (tset t r) =i
        if valid (tset t r) then preorder t else [::].
Proof. by move=>x; rewrite valid_dom_tset. Qed.

Lemma dom_tset (t : tree ptr) r :
        valid (tset t r) -> dom (tset t r) =i t.
Proof. by move=>V x; rewrite dom_tset_ord V in_preorder. Qed.

Lemma dom_tsetE (t : tree ptr) r :
        dom (tset t r) =i [pred x | valid (tset t r) && (x \in t)].
Proof. by move=>x; rewrite inE dom_tset_ord -in_preorder; case: ifP. Qed.

Lemma size_dom_tset (t : tree ptr) r :
        valid (tset t r) ->
        size (dom (tset t r)) = size (preorder t).
Proof.
move=>V; apply/eqP; rewrite -uniq_size_uniq ?uniq_dom -?(valid_tset t r) //.
by move=>x; rewrite dom_tset_ord V.
Qed.

Lemma range_tset (t : tree ptr) r :
        valid (tset t r) -> range (tset t r) =i [:: r].
Proof.
elim/tree_ind2: t=>a ts IH. rewrite tsetE /= => V x.
rewrite rangePtUn inE validPtUn (validX V) (validPtUnD V) inE /= eq_sym.
case: eqVneq=>//= N; apply/negP=>/mem_rangeX [k].
case/bigInX=>i /[dup] X /mem_seqP X' /mem_range. rewrite IH //.
- by rewrite inE (negbTE N).
by apply: big_validV (validX V) X.
Qed.

Lemma domeq_tlay_tset (t : tree ptr) r1 r2 :
        {in t, forall x, x != null} ->
        dom_eq (tlay t r1) (tset t r2).
Proof.
elim/tree_ind1: t r1 r2=>a ts IH r1 r2 Tn.
rewrite tlayE tsetE /= domeqPtUn ?Tn // big_domeqUn //.
by move=>x X; apply: IH=>// z Z; apply: Tn (in_tnode2 X Z).
Qed.

Lemma valid_tlayE (t : tree ptr) r :
        valid (tlay t r) -> {in t, forall x, x != null}.
Proof.
elim/tree_ind1: t r=>a ts IH r; rewrite tlayE /= => V x; rewrite in_tnode.
case/orP=>[/eqP ->|]; first by rewrite (validPtUn_cond V).
case/hasPIn=>y Y; apply: IH =>//; apply: (big_validV (validX V) Y).
Qed.

Lemma valid_tlay (t : tree ptr) r :
        valid (tlay t r) =
        valid (tset t r) && all (fun x => x != null) (preorder t).
Proof.
apply/idP/idP; last first.
- by case/andP=>V /tallP W; rewrite (domeqVE (domeq_tlay_tset r r W)).
move/[dup]=>V /valid_tlayE /[dup] N /tallP ->.
by rewrite -(domeqVE (domeq_tlay_tset r r N)) V.
Qed.

Lemma valid_tlayN (t : tree ptr) r :
        valid (tlay t r) -> valid (tset t r).
Proof. by rewrite valid_tlay=>/andP []. Qed.

Lemma dom_tlay (t : tree ptr) r :
        valid (tlay t r) -> dom (tlay t r) =i t.
Proof.
rewrite valid_tlay=>/andP [V /tallP A] x.
by rewrite -(dom_tset V) (domeqDE (domeq_tlay_tset r r A)).
Qed.

Lemma dom_tlayE (t : tree ptr) r :
        dom (tlay t r) =i [pred x | valid (tlay t r) && (x \in t)].
Proof.
move=>x; apply/idP/idP; last by rewrite inE; case/andP=>V; rewrite dom_tlay.
by move=>D; rewrite inE (dom_valid D) -(dom_tlay (dom_valid D)).
Qed.

Lemma size_dom_tlay (t : tree ptr) r :
        valid (tlay t r) ->
        size (dom (tlay t r)) = size (preorder t).
Proof.
move=>V; apply/eqP; rewrite -uniq_size_uniq ?uniq_dom //.
- by rewrite -(valid_tset t r) (valid_tlayN V).
by move=>x; rewrite dom_tlay // in_preorder.
Qed.

(* no strong range_tlay lemma; weak one below *)

(***********************************)
(* parent-child relation and roots *)
(* for inverted trees              *)
(***********************************)

Lemma find_tset x r t :
        find x (tset t r) =
        if valid (tset t r) && (x \in t) then Some r else None.
Proof.
case V : (valid (tset t r))=>/=; last first.
- by move/invalidE: (negbT V)=>->; rewrite find_undef.
rewrite -(dom_tset V); case: dom_find=>// v E _.
elim/tree_ind1: t V E=>a ts IH; rewrite tsetE /= => V.
rewrite !findPtUn2 //; case: (x =P a)=>//= _.
case/big_find_someX=>i X /[dup] D /In_find/In_valid W.
by apply: IH X W (D).
Qed.

Lemma In_tsetP x r t:
        reflect ((x, r) \In tset t (rt t))
                [&& valid (tset t (rt t)), x \in t & r == rt t].
Proof.
apply/(iffP idP); rewrite In_find find_tset.
- by case/and3P=>->-> /eqP ->.
by case: ifP=>// /andP [->->][->] /=.
Qed.

Lemma find_tlayTp (x : ptr) (t : tree ptr) (p : dynamic id) r :
        find x (tlay t r) = Some p ->
        exists x : ptr, p = idyn x.
Proof.
elim/tree_ind1: t r=>a t IH r; rewrite tlayE /=.
move/[dup]=>/In_find/In_valid V; rewrite findPtUn2 //.
case: eqP=>[_ [<-]|_]; first by exists r.
by case/big_find_someX=>z Z /(IH _ Z).
Qed.

Lemma tlay_rt x (p : ptr) t r :
        find x (tlay t r) = Some (idyn p) ->
        if x == rt t then p = r else (p != x) && (p \in t).
Proof.
elim/tree_ind1: t r=>a ts IH r; rewrite tlayE /= => /[dup]/In_find/In_valid V.
rewrite findPtUn2 // in_tnode; case: eqVneq=>[_ [/inj_pair2]|N] //.
case/big_find_someX=>t T /(IH _ T) H; case: ifP H N=>[_ ->|_].
- by rewrite eqxx // eq_sym =>->.
by case/andP=>-> H _; case: orP=>//; elim; right; apply/hasPIn; exists t.
Qed.

Lemma tlay_rt_loop t x :
        find x (tlay t (rt t)) = Some (idyn x) -> x = rt t.
Proof. by move/tlay_rt; rewrite eqxx /=; case: eqP. Qed.

Lemma tlay_rt_rt (p : ptr) t r :
        find (rt t) (tlay t r) = Some (idyn p) -> p = r.
Proof. by move/tlay_rt; rewrite eqxx. Qed.


(********************)
(********************)
(* inverted forests *)
(********************)
(********************)

Definition flay ts := foldr (fun t h => tlay t (rt t) \+ h) Unit ts.
Definition fset ts := foldr (fun t h => tset t (rt t) \+ h) Unit ts.

Lemma flayE ts : flay ts = \big[join/Unit]_(t <- ts) (tlay t (rt t)).
Proof. by elim: ts=>[|t ts IH] /=; [rewrite big_nil|rewrite big_cons IH]. Qed.

Lemma fsetE ts : fset ts = \big[join/Unit]_(t <- ts) (tset t (rt t)).
Proof. by elim: ts=>[|t ts IH] /=; [rewrite big_nil|rewrite big_cons IH]. Qed.

Lemma find_flayTp (x : ptr) (ts : seq (tree ptr)) (p : dynamic id) :
        find x (flay ts) = Some p ->
        exists y : ptr, p = idyn y.
Proof.
elim: ts=>[|t ts IH] //= /[dup] /In_find/In_valid V; rewrite findUnL //.
by case: ifP=>_; [apply: find_tlayTp | apply: IH].
Qed.

Lemma In_fsetP x r ts :
        reflect ((x, r) \In fset ts)
                (valid (fset ts) && has (fun t => (x \in t) && (r == rt t)) ts).
Proof.
rewrite fsetE; apply/(iffP idP).
- case/andP=>V /hasP [i] /mem_seqP X /andP [H1 H2].
  by apply: bigIn (V) (X) _; apply/In_tsetP; rewrite H1 H2 (big_validV V).
move/[dup]/In_valid=>-> /bigInX [i] /mem_seqP X /In_tsetP /andP [V H].
by apply/hasP; exists i.
Qed.

Lemma dom_fset (ts : seq (tree ptr)) x :
        valid (fset ts) ->
        x \in dom (fset ts) = has (fun t => x \in t) ts.
Proof.
elim: ts=>[|t ts IH] //= V.
by rewrite domUn V inE /= IH ?dom_tset ?(validX V).
Qed.

Lemma dom_fsetE (ts : seq (tree ptr)) :
        dom (fset ts) =i
        [pred x | valid (fset ts) && has (fun t => x \in t) ts].
Proof.
move=>x; rewrite inE.
case V : (valid (fset ts))=>/=; first by apply: dom_fset.
by move/invalidE: (negbT V)=>->; rewrite dom_undef.
Qed.

Lemma range_fsetE ts :
        range (fset ts) =i
        [pred x | valid (fset ts) && has (fun t => x == rt t) ts].
Proof.
elim: ts=>[|t ts IH] //= x. 
rewrite rangeUn inE; case V : (valid _)=>//=.
by rewrite range_tset ?inE ?IH ?(validX V).
Qed.

Lemma range_fset ts x :
        valid (fset ts) ->
        x \in range (fset ts) = has (fun t => x == rt t) ts.
Proof. by move=>V; rewrite range_fsetE V inE. Qed.


Lemma valid_fset_tset (ts : seq (tree ptr)) :
        valid (fset ts) -> 
        {in ts, forall i, valid (tset i (rt i))}.
Proof. by move=>+ i Hi; rewrite fsetE big_valid_seq=>/andP [/allP /(_ i Hi)]. Qed.

Lemma valid_flay_tlay (ts : seq (tree ptr)) :
        valid (flay ts) -> 
        {in ts, forall i, valid (tlay i (rt i))}.
Proof. by move=>+ i Hi; rewrite flayE big_valid_seq=>/andP [/allP /(_ i Hi)]. Qed.

Lemma dom_flay (ts : seq (tree ptr)) x :
        valid (flay ts) ->
        x \in dom (flay ts) = has (fun t => x \in t) ts.
Proof.
move=>V; rewrite flayE big_domUn inE -flayE V; apply: eq_in_has=>i H.
by rewrite dom_tlay // (valid_flay_tlay V).
Qed.

Lemma dom_flayE (ts : seq (tree ptr)) :
        dom (flay ts) =i
        [pred x | valid (flay ts) && has (fun t => x \in t) ts].
Proof.
move=>x; case V : (valid _)=>/=; last first.
- by move/invalidE: (negbT V)=>->; rewrite dom_undef.
by rewrite inE dom_flay.
Qed.

Lemma valid_flay_fset (ts : seq (tree ptr)) :
        valid (flay ts) = valid (fset ts) &&
        all (fun t => all (fun i => i != null) (preorder t)) ts.
Proof.
elim: ts=>[|t ts IH] //=.
rewrite !validUnAE IH -!andbA valid_tlay /=.
case V1 : (valid _)=>//=.
case V2 : (valid _)=>/=; last by rewrite andbF.
case A1 : (all _)=>/=; last by rewrite andbF.
case A2 : (all _)=>/=; last by rewrite andbF.
rewrite andbT !all_predC; rewrite V2 A2 /= in IH; congr (~~ _).
have /eq_has -> : dom (tlay t (rt t)) =i dom (tset t (rt t)).
- by move=>x; rewrite dom_tlay ?valid_tlay ?V1 ?A1 ?dom_tset.
by apply: eq_has_r=>x; rewrite dom_flay // dom_fset.
Qed.

Lemma dom_flay_fset (ts : seq (tree ptr)) :
        all (fun t => all (fun i => i != null) (preorder t)) ts ->
        dom (flay ts) = dom (fset ts).
Proof.
move=>A; apply/domE=>x; rewrite dom_flayE dom_fsetE !inE valid_flay_fset A /=.
by rewrite andbT.
Qed.

Lemma subvalid_flay (ts : seq (tree ptr)) :
        valid (flay ts) -> valid (fset ts).
Proof. by rewrite valid_flay_fset=>/andP []. Qed.

Lemma subdom_flay (ts : seq (tree ptr)) :
        {subset dom (flay ts) <= dom (fset ts)}.
Proof.
move=>x /[dup] /dom_valid; rewrite valid_flay_fset=>/andP [V A].
by rewrite dom_flay_fset.
Qed.

Lemma valid_flayN2 t (ts : seq (tree ptr)) :
         valid (tlay t (rt t) \+ flay ts) ->
         valid (tset t (rt t) \+ fset ts).
Proof.
by rewrite (_ : valid _ = valid (flay (t :: ts))) // => /subvalid_flay.
Qed.

Lemma flay_rt x (p : ptr) ts :
        find x (flay ts) = Some (idyn p) ->
        if x \in range (fset ts) then p == x
        else (p != x) && has (fun t => (x \in t) && (p \in t)) ts.
Proof.
elim: ts=>[|t ts IH] /=; first by rewrite find0E.
move/[dup]=>/In_find/In_valid V.
rewrite findUnL // rangeUn inE (valid_flayN2 V) /=.
rewrite dom_tlayE inE (validX V) /=.
rewrite range_tset ?(valid_tlayN (validX V)) // inE.
case: eqVneq=>[->|N] /=; first by rewrite rt_in=>/tlay_rt_rt ->; rewrite eqxx.
case: ifP=>X // /tlay_rt; rewrite (negbTE N)=>/andP [P1 P2].
rewrite {P1}(negbTE P1) range_fset ?(subvalid_flay (validX V)) // ifN ?P2 //.
apply/hasPn=>y Ty; apply: contra N=>/eqP ?; subst x; exfalso.
apply: (dom_inNLX (k:=rt y) V).
- by rewrite dom_tlayE inE (validX V).
by rewrite dom_flayE inE (validX V); apply/hasP; exists y=>//; rewrite rt_in.
Qed.

Lemma flay_rt_domL x (p : ptr) ts :
        find x (flay ts) = Some (idyn p) -> x \in dom (fset ts).
Proof. by move=>H; apply: subdom_flay (find_some H). Qed.

Lemma flay_rt_domR x (p : ptr) ts :
        find x (flay ts) = Some (idyn p) -> p \in dom (fset ts).
Proof.
move/[dup]=>/In_find/In_dom /= H /flay_rt.
case: ifP=>[_ /eqP ->|_]; first by apply: subdom_flay.
case/andP=>_ H1; rewrite dom_fset; first by apply: sub_has H1=>z /andP [].
by apply: subvalid_flay (dom_valid H).
Qed.

Lemma size_dom_flay ts :
        valid (flay ts) ->
        size (dom (flay ts)) = \sum_(t <- ts) size (preorder t).
Proof.
elim: ts=>[|t ts IH /=]; first by rewrite big_nil.
move=>V; rewrite big_cons size_domUn //.
by rewrite -IH ?(validX V) // -(size_dom_tlay (validX V)).
Qed.

Lemma dom_flay_big (ts : seq (tree ptr)) :
        valid (flay ts) ->
        dom (flay ts) =i \big[cat/[::]]_(t <- ts) preorder t.
Proof.
move=>V x; rewrite flayE big_domUn inE -flayE V big_cat_mem_has /=.
by apply: eq_in_has=>i H; rewrite dom_tlay ?in_preorder ?(valid_flay_tlay V H).
Qed.

Lemma flay_uniq ts :
        valid (flay ts) ->
        uniq (\big[cat/[::]]_(t <- ts) preorder t).
Proof.
move=>V; rewrite -(eq_uniq _ (dom_flay_big V)) ?uniq_dom //.
by rewrite size_dom_flay ?size_big_cat.
Qed.

Lemma flay_mem_eq x i j ts :
        valid (flay ts) ->
        x \in i -> i \in ts ->
        x \in j -> j \in ts -> i = j.
Proof.
move=>V Xi /[dup] Ti /mem_seqP Ti' Xj /[dup] Tj /mem_seqP Tj'.
apply: big_cat_uniq_pairwise (flay_uniq V) Ti' Tj' _.
by apply/hasP; exists x=>/=; rewrite in_preorder.
Qed.

Lemma fset_pts_rev x r ts :
        valid (flay ts) ->
        (x, r) \In fset ts ->
        exists2 p, [pcm x :-> p <= flay ts] & (p, r) \In fset ts.
Proof.
move=>V /[dup] H /In_fsetP /andP [Vs] /hasP [i] Ti /andP [Xi /eqP E].
have : x \in dom (flay ts) by rewrite dom_flay // -dom_fset // (In_dom H).
case/In_domX=>_ /In_find/[dup] /find_flayTp [p -> F].
exists p; first by exists (free (flay ts) x); apply: um_eta2.
move/flay_rt: F. case: ifP=>[_ /eqP ->|_] //.
case/andP=>N /hasP [j Tj] /andP [Xj P].
apply/In_fsetP; rewrite Vs; apply/hasP; exists j=>//.
by rewrite P E (flay_mem_eq V Xi Ti Xj Tj) eqxx.
Qed.

Lemma froot_loop x r ts :
        (x, r) \In fset ts ->
        find x (flay ts) = Some (idyn x) ->
        x = r.
Proof.
elim: ts r=>[|t ts IH] r //= /In_find H1 H2.
move: (dom_valid (find_some H1)) (dom_valid (find_some H2))=>V1 V2.
move: H1 H2; rewrite !findUnL ?(dom_tset,dom_tlay,validL V1,validL V2) //.
case A: (x \in t).
- rewrite find_tset ifT; first by case=>E; move/tlay_rt_loop=>K; rewrite K -E.
  apply/andP; split=>//; first by apply: validL V1.
by rewrite -In_find; apply: IH.
Qed.

Definition change_ts (ts : seq (tree ptr)) (a b : tree ptr) :=
  if a == b then ts
  else TNode (rt b) (a :: ch b) ::
       filter (fun x => (x != a) && (x != b)) ts.

Lemma flay_cons (a : tree ptr) b : flay (a :: b) = flay [:: a] \+ flay b.
Proof. by rewrite !flayE !big_cons !big_nil unitR. Qed.

Lemma flay_tree (a: tree ptr):
        flay ([:: a]) = tlay a (rt a).
Proof. by rewrite flayE big_cons big_nil unitR. Qed.

Lemma flay_uniq_ts ts : valid (flay ts) -> uniq ts.
Proof.
move=>/flay_uniq/uniq_big_catE [_ H _]; apply: count_mem_uniq=>t.
case T : (t \in ts); last by apply/count_memPn; apply: negbT.
by apply: (H t (rt t))=>//; rewrite in_preorder rt_in.
Qed.

Lemma nochange_mapv (K : ordType) (V : eqType) (m : umap K V) b x :
        valid m ->
        x \notin range m ->
        mapv [fun v => v with x |-> b] m = m.
Proof.
move=>W /negP R; apply: umem_eq=>[|//|[k v]]; first by rewrite pfV.
rewrite In_omapX /=; split=>[[w]|H].
- by case: (w =P x)=>[->{w} /mem_range/R|_ /[swap][[]->]//].
by exists v=>//; case: (v =P x) H=>// -> /mem_range/R.
Qed.

Lemma change_tset ta a b:
        valid (tset ta a) ->
        mapv [fun v => v with a |-> b] (tset ta a) = tset ta b.
Proof.
elim/tree_ind2: ta a=>c ts IH a //; rewrite !tsetE /= => V.
rewrite omapVUn omapPt /= eq_refl big_omapVUn !(validX V).
congr (_ \+ _); apply: eq_big_seq=>i /[dup] K /mem_seqP K'.
by rewrite IH // (big_validV (validX V) K').
Qed.

(*******************)
(* Shape predicate *)
(*******************)

Definition shape rs h := exists ts, [/\ h = flay ts, rs = fset ts & valid h].

Lemma shapeV rs h : shape rs h -> valid rs.
Proof. by case=>ts [->->]; rewrite valid_flay_fset=>/andP []. Qed.

(*******)
(* NEW *)
(*******)

(* Creates a new equivalence class with a single element *)

Program Definition newT :
  STsep {m} (shape m, [vfun r => shape (r \\-> r \+ m)]) :=
  Do (p <-- alloc null;
      p ::= p;;
      ret p).
Next Obligation.
case=>m [] h [ts] [->-> V]. step=>p. do !step. move=>V2.
by  exists (TNode p nil :: ts); split.
Qed.

(********)
(* FIND *)
(********)

(* Returns the canonical representative of the equivalence class of an element*)

Definition find_tp (x : ptr) :=
  STsep {rs r} (fun h => shape rs h /\ (x, r) \In rs,
                [vfun res h => shape rs h /\ res = r]).

Program Definition find1 (x : ptr) : find_tp x :=
  Do (let root := ffix (fun (go : forall x, find_tp x) (x : ptr) =>
        Do (p <-- !x;
            if x == p then ret p else go p))
      in root x).
Next Obligation.
move=>_ go x [rs][r] [] h //= [[ts [->-> V]] H].
case/(fset_pts_rev V): (H)=>p [j E] K. rewrite E in V; rewrite E; step.
case: (x =P p) E =>[->|N] E; apply: vrfV=>V1.
- step=>_. split=>//; first by exists ts; split=>//=.
  by apply: froot_loop K _; rewrite E findPtUn.
apply: [gE fset ts, r] => //=; first by do !split=>//=; exists ts; split.
Qed.
Next Obligation.
move=>x [rs][r][] h //= [[ts [->-> V]] H].
apply: [gE fset ts, r]=>//=.
by do !split=>//=; exists ts; split.
Qed.

(*********)
(* UNION *)
(*********)

(* Joins the equivalence classes of the two arguments *)

Definition union_tp (x y : ptr) := STsep {rx ry m}
   (fun h => [/\ shape m h, (x, rx) \In m & (y, ry) \In m],
   [vfun res h => shape (mapv [fun v => v with rx |-> ry] m) h /\
                        res = ry]).

Program Definition union (x y : ptr) : union_tp x y :=
  Do (x_rt <-- find1 x;
      y_rt <-- find1 y;
      x_rt ::= y_rt;;
      ret y_rt).
Next Obligation.
move=>x y [a][b][_] [] _ /= [[ts [->-> Vh]] Hx Hy].
apply: [stepE fset ts, a]=>//=; first by do !split=>//; exists ts; split.
move=>_ _ [[ts1] [-> Eq1 V1] ->]; rewrite Eq1 in Hy Hx {Vh}.
apply: [stepE fset ts1, b]=>//=; first by split=>//; exists ts1; by do !split.
move=>_ _ [[ts2] [-> Eq2 V2] ->]; rewrite Eq2 in Hy Hx {V1}.
move/In_fsetP: (Hx) => /andP [V] /hasP [ta J] /andP [X /eqP rtA].
move/In_fsetP: (Hy) => /andP [_] /hasP [tb K] /andP [Y /eqP rtB].
have B: a \in ta by rewrite rtA rt_in.
have C: b \in tb by rewrite rtB rt_in.
have: has (fun t => a \in t) ts2 by apply/hasP; exists ta.
rewrite -dom_flay //.
case/In_domX=>_ /[dup] /In_find/find_flayTp [v] -> /In_find Da.
move/flay_rt: (Da); move/In_range: (Hx)=>/mem_seqP U; rewrite ifT; last by [].
move/eqP=>EqV; rewrite EqV in Da; clear EqV v.
move/heap_eta2: (Da)=>Hts; rewrite Hts; do 2!step; move=>Hv.
split=>//; exists (change_ts ts2 ta tb); split=>//=.
(*CASE 1: a :-> b \+ free (flay ts) a = flay (change_ts ts ta tb) *)
- rewrite /change_ts /=; case: eqP.
  - by move=>E; rewrite rtB -E -rtA.
  move=>N; rewrite flay_cons flay_tree tlayE /= big_cons tlayE /= -rtB.
  rewrite -rtA -!joinA joinCA; congr (_ \+ _); move:(V2).
  rewrite flayE (bigD1_seq ta) //=; last by apply: flay_uniq_ts.
  rewrite -big_filter (bigD1_seq tb) =>//=; last first.
  by rewrite filter_uniq //; apply: flay_uniq_ts.
  by rewrite mem_filter K andbT; case: eqP=>// E; rewrite E in N.
  rewrite tlayE -rtA -!joinA => Vh'.
  rewrite freePtUn // tlayE -rtB -joinCA -!joinA; congr (_ \+ _).
  rewrite joinCA; do 2!congr (_ \+ _); rewrite -big_filter -filter_predI.
  by rewrite seqext.filter_predIC big_filter //= flayE  -big_filter.
(*CASE 2: mapv [fun v => v with a |-> b] c = fset (change_ts ts ta tb) *)
move: (V); rewrite  Eq1 Eq2 !fsetE /change_ts; case: eqP.
- move=>E; subst tb; rewrite rtA rtB -rtA (_ : fun_of_simpl _ = id).
  - by rewrite mapv_id.
  by apply: fext=>z /=; case: eqP.
move=>N; rewrite big_cons tsetE /= -rtB big_cons (bigD1_seq ta) //=; last first.
- by apply: flay_uniq_ts.
simpl; rewrite -big_filter (bigD1_seq tb)=>//=; last first.
- by rewrite filter_uniq //; apply: flay_uniq_ts.
- by rewrite mem_filter K andbT; case: eqP N=>// ->.
(*Case 2.1: mapv tset a = tset b *)
rewrite -rtA -rtB big_filter_cond; move=>V'.
move/validL: (V'); move/validR: (V'); move/[dup]=>/validL Vb /validR Vc Va.
rewrite omapUn // change_tset // -!joinA joinCA; congr (_ \+ _).
rewrite omapUn; last by rewrite (validX V').
(*Case 2.2: tset of bigger tree doesn't change *)
rewrite nochange_mapv //; last first.
rewrite range_tset // mem_seq1; case: eqP =>// eqAB.
- have: ta = tb by rewrite -eqAB in C; rewrite (flay_mem_eq V2 B J C K).
  by move/eqP: N => /eqP eqF eqT; rewrite eqT in eqF.
rewrite tsetE -rtB joinA big_filter //; congr (_ \+ _).
(*Case 2.3: tset of trees different than a and b don't change *)
apply: nochange_mapv =>//; apply/negP; move/mem_rangeX; case=>k H.
case: (bigInXP H)=>j [/mem_seqP X1 /andP [X2 X3]].
move/mem_range; rewrite range_tset //; last by apply: valid_fset_tset X1.
rewrite inE => /eqP X4; move/negP: X2; apply; apply/eqP.
by apply: flay_mem_eq X1 B J=>//; rewrite X4 rt_in.
Qed.

(*********)
(* Tests *)
(*********)

Program Definition test1:
  STsep (fun h => shape Unit h,
         [vfun y h => exists x, shape (x \\-> y \+ y \\-> y) h]) :=
  Do (x <-- newT;
      y <-- newT;
      res <-- union x y;
      ret res).
Next Obligation.
case=>i H.
apply: [stepE Unit]=>//= x j; rewrite unitR=>X.
apply: [stepE x \\-> x]=>//= y k {X} /[dup]X [ts [A m V]].
rewrite A in V; move: (V); rewrite valid_flay_fset.
move=> /andP [ V1 _] //; rewrite -m in V1.
apply: [stepE x, y, y \\-> y \+ x \\-> x]=>//=.
move=>a h [B ->]; step=>Vh; exists x; move: B.
rewrite omapUn // nochange_mapv; first by rewrite omapPt //= ifT // joinC.
- by apply: validX V1.
rewrite rangePt //; apply/eqP=>N; rewrite N in X.
by move/shapeV: X; rewrite invalidX.
Qed.

Program Definition test2 (x: ptr):
  STsep {y} (fun h => shape (x \\-> y \+ y \\-> y) h,
            [vfun res h => shape (x \\-> y \+ y \\-> y) h /\ res = y]) :=
  Do (res <-- find1 x;
      ret res).
Next Obligation.
move=>a [b []] _ [ts][-> B C].
apply: [stepE fset ts, b]=>//=; last first.
- by move=>p h [H ->]; step=>_; split=>//; rewrite B.
move: (C); rewrite valid_flay_fset; move=>/andP [V1 _].
split=>//; first by exists ts; split.
rewrite -B; apply: InL; first by rewrite B.
by apply: In_condPt.
Qed.
