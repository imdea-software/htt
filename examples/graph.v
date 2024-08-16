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

From HB Require Import structures.
From Coq Require Import ssreflect ssrfun.
From mathcomp Require Import ssrbool eqtype ssrnat seq path.
From pcm Require Import options axioms pred prelude seqext.
From pcm Require Import pcm unionmap natmap autopcm automap.

(*************)
(*************)
(* Pregraphs *)
(*************)
(*************)

(* Pregraphs are natmaps, mapping each graph node x into a node sequence *)
(* that enumerates the children of x (x's adjacency list). *)
(* Pregraph differs from graph, in that edges can *dangle*; that is *)
(* terminate with a node that isn't in the graph's domain. *)
(* Dangling edges are allowed because they enable encoding positional *)
(* information about nodes, as usual in pointer structures. *)
(* For example, if there are 3 links for x, and null is the 2nd link, *)
(* that encodes that the second child of x doesn't exist. *)
(* Non-null dangling links are technically possible, *)
(* but are treated same as null. *)

(* Pregraph differs from fingraph (of mathcomp) *)
(* in that the set of nodes is drawn from an infinite set *)
(* not from a fixed finite set. *)

Notation node := nat.
Record pregraph := Pregraph {pregraph_base : @UM.base node nat_pred (seq node)}.

Section PregraphUMC.
Implicit Type f : pregraph.
Local Coercion pregraph_base : pregraph >-> UM.base.
Let pg_valid f := @UM.valid nat nat_pred (seq nat) f.
Let pg_empty := Pregraph (@UM.empty nat nat_pred (seq nat)).
Let pg_undef := Pregraph (@UM.Undef nat nat_pred (seq nat)).
Let pg_upd k v f := Pregraph (@UM.upd nat nat_pred (seq nat) k v f).
Let pg_dom f := @UM.dom nat nat_pred (seq nat) f. 
Let pg_assocs f := @UM.assocs nat nat_pred (seq nat) f. 
Let pg_free f k := Pregraph (@UM.free nat nat_pred (seq nat) f k).
Let pg_find k f := @UM.find nat nat_pred (seq nat) k f. 
Let pg_union f1 f2 := Pregraph (@UM.union nat nat_pred (seq nat) f1 f2).
Let pg_empb f := @UM.empb nat nat_pred (seq nat) f. 
Let pg_undefb f := @UM.undefb nat nat_pred (seq nat) f.
Let pg_from (f : pregraph) : UM.base _ _ := f. 
Let pg_to (b : @UM.base nat nat_pred (seq nat)) : pregraph := Pregraph b.
Let pg_pts k v := Pregraph (@UM.pts nat nat_pred (seq nat) k v).

Lemma pregraph_is_umc : 
        union_map_axiom pg_valid pg_empty pg_undef pg_upd pg_dom 
                        pg_assocs pg_free pg_find pg_union pg_empb 
                        pg_undefb pg_pts pg_from pg_to. 
Proof. by split=>//; split=>[|[]]. Qed.

HB.instance Definition _ := 
  isUnion_map.Build node nat_pred (seq node) pregraph pregraph_is_umc. 
End PregraphUMC.

HB.instance Definition _ := isNatMap.Build (seq node) pregraph.
HB.instance Definition _ := 
  hasDecEq.Build pregraph (@union_map_eqP node _ (seq node) pregraph).
Canonical pregraph_PredType : PredType (node * (seq node)) := 
  um_PredType pregraph.
Coercion Pred_of_history (x : pregraph) : {Pred _} := 
  [eta Mem_UmMap x].

Notation "x &-> v" := (ptsT pregraph x v) (at level 30).

(**************************)
(* Links, children, edges *)
(**************************)

(* Links of x includes all edges outgoing from x *)
(* and may explicitly include nodes that aren't in dom g *)
(* (i.e., are dangling, null or non-null) *)
Definition links (g : pregraph) x := oapp id [::] (find x g).

(* children x removes dangling edges (null or non-null) from links *)
Definition children (g : pregraph) x : seq node :=
  filter (mem (dom g)) (links g x).

(* edge is applicative variant of children *)
(* thus, dangling edges (null or non-null) are *not* edges. *)
Definition edge g : rel node := mem \o children g.
Arguments edge g x y : simpl never.

(* links lemmas *)

Lemma links_undef x : links undef x = [::].
Proof. by []. Qed.

Lemma links_unit x : links Unit x = [::].
Proof. by []. Qed.

Lemma linksND g x :
        x \notin dom g ->
        links g x = [::].
Proof. by rewrite /links/oapp; case: dom_find. Qed.

Lemma linksUnL g1 g2 x : 
        valid (g1 \+ g2) ->
        links (g1 \+ g2) x = 
        if x \in dom g1 then links g1 x else links g2 x.
Proof. by move=>V; rewrite /links/oapp findUnL //; case: dom_find. Qed.

Lemma linksUnR g1 g2 x : 
        valid (g1 \+ g2) ->
        links (g1 \+ g2) x = 
        if x \in dom g2 then links g2 x else links g1 x.
Proof. by rewrite joinC=>/linksUnL; apply. Qed.

Lemma size_links g x : 
        size (links g x) > 0 ->
        x \in dom g.
Proof. by rewrite /links/oapp; case: dom_find. Qed.

Lemma linksD (g : pregraph) x y : 
        y \in links g x ->
        x \in dom g.
Proof. by move=>X; apply: size_links; case: (links g x) X. Qed.

Lemma In_graph (g : pregraph) x xs : 
        (x, xs) \In g -> 
        xs = links g x.
Proof. by rewrite /links/oapp=>/In_find ->. Qed.

Lemma In_graphX (g : pregraph) x : 
        x \in dom g ->
        (x, links g x) \In g.
Proof. 
by move=>Dx; apply/In_find; rewrite /links/oapp; case: dom_find Dx. 
Qed.

Lemma range_links (g : pregraph) x : 
        x \in dom g ->
        links g x \in range g.
Proof. by move/In_graphX/mem_range. Qed.

Lemma links_umfiltk g p x : 
        links (um_filterk p g) x =i 
        if p x then links g x else [::].
Proof. by move=>i; rewrite /links find_umfiltk; case: (p x). Qed.

(* children lemmas *)

Lemma children_undef x : children undef x = [::].
Proof. by []. Qed.

Lemma children_unit x : children Unit x = [::].
Proof. by []. Qed.

Lemma childrenND g x :
        x \notin dom g ->
        children g x = [::].
Proof. by rewrite /children=>/linksND ->. Qed.

Lemma childrenD g x : 
        {subset children g x <= dom g}.
Proof. by move=>y; rewrite /children mem_filter; case/andP. Qed.

Lemma childrenUnL g1 g2 x : 
        valid (g1 \+ g2) ->
        {subset children g1 x <= children (g1 \+ g2) x}.
Proof.
move=>V y; rewrite /children !mem_filter /= =>/andP [Dy Ly]. 
by rewrite domUn inE V Dy linksUnL //= (linksD Ly).
Qed.

Lemma childrenUnR g1 g2 x : 
        valid (g1 \+ g2) ->
        {subset children g2 x <= children (g1 \+ g2) x}.
Proof. by rewrite joinC; apply: childrenUnL. Qed.

Lemma children_links (g : pregraph) x : 
        {subset children g x <= links g x}.
Proof. by move=>z; rewrite /children mem_filter=>/andP []. Qed.

(* if x is node in g then g x contains all children of x *)
(* and maybe some more nodes that aren't in g *)
Lemma range_children (g : pregraph) x : 
        x \in dom g ->
        exists2 xs, xs \in range g & 
                    {subset children g x <= xs}.
Proof.
move=>Dx; exists (links g x); first by apply: range_links.
by apply: children_links.
Qed.

Lemma children_umfiltk g p x y : 
        y \in children (um_filterk p g) x = 
        [&& p x, p y & y \in children g x].
Proof. 
rewrite /children !mem_filter /= links_umfiltk dom_umfiltk inE -andbA.
by case: (p x)=>//=; rewrite !andbF.
Qed. 

(* edge lemmas *)

Lemma edge_undef x y : edge undef x y = false. 
Proof. by rewrite /edge/= children_undef. Qed.

Lemma edge_unit x y : edge Unit x y = false. 
Proof. by rewrite /edge/= children_unit. Qed.

Lemma edge_children g x y : 
        edge g x y = (y \in children g x).
Proof. by []. Qed.

Lemma edgeUnL g1 g2 x y :
        valid (g1 \+ g2) ->
        edge g1 x y -> 
        edge (g1 \+ g2) x y.
Proof. by move=>V; apply: childrenUnL. Qed.

Lemma edgeUnR g1 g2 x y :
        valid (g1 \+ g2) ->
        edge g2 x y -> 
        edge (g1 \+ g2) x y.
Proof. by move=>V; apply: childrenUnR. Qed.

Lemma edgeD g x y : 
        edge g x y -> 
        (x \in dom g) * (y \in dom g).
Proof.
rewrite /edge/= => H; split; last by apply: childrenD H. 
by apply: contraLR H=>/childrenND ->.
Qed.

Lemma edge_links g x y :
        edge g x y = (y \in dom g) && (y \in links g x).
Proof.
rewrite /edge/children/links/oapp/= mem_filter /=.
by case: dom_find.
Qed.

Lemma path_dom g x xs :
        path (edge g) x xs ->
        {subset xs <= dom g}.
Proof.
elim: xs x=>[|a xs IH] x //= /andP [/edgeD [_ He] /IH].
by apply: subset_consLI He. 
Qed.

Lemma edge_umfiltk g p x y :   
        edge (um_filterk p g) x y = 
        [&& p x, p y & edge g x y].
Proof. by rewrite /edge /= children_umfiltk. Qed.

Lemma edge_umfiltkE g p : 
        {in predC p &, edge (um_filterk (predC p) g) =2 edge g}.
Proof. by move=>x y; rewrite !inE => X Y; rewrite edge_umfiltk /= X Y. Qed.

(***********************)
(* Depth-first search  *)
(***********************)

(* lifts dfs from mathcomp fingraph to pregraphs *)

(* list of nodes traversed by depth-first search of g *)
(* at depth n, starting from x, and avoiding v. *)
(* Definition uses children, not links; *)
(* thus, it doesn't follow dangling edges *)
(* and dfs can't express reachability to an outside node. *)
(* If the latter is desired, it can be separately defined *)
(* as a conjunct of dfs and links properties. *)

Fixpoint dfs (g : pregraph) (n : nat) (v : seq node) x :=
  if (x \notin dom g) || (x \in v) then v else
  if n is n'.+1 then foldl (dfs g n') (x :: v) (children g x) else v.

Lemma dfs_notin g n v x : 
        x \notin dom g ->
        dfs g n v x = v.
Proof. by elim: n=>[|n IH] /= ->. Qed.

Lemma subset_dfs g n v x : 
        {subset v <= foldl (dfs g n) v x}.
Proof.
elim: n x v => [|n IHn] /=; elim=>[|x xs IHx] v //=.
- by case: ifP.
move=>y Hy; apply: IHx; case: ifP=>//= _.
by apply: IHn; rewrite inE Hy orbT.
Qed.

(* avoidance set is bound by g *)
Lemma subset_foldl_dfs_dom g n v x :
        {subset v <= dom g} ->
        {subset foldl (dfs g n) v x <= dom g}.
Proof.
elim: n x v=>[|n IHn]; elim=>[|x xs IHx] v //=.
- by case: ifP=>_; apply: IHx.
case: ifP; first by case: (x \in dom g)=>//= H; apply: IHx.
case Dx: (x \in dom g)=>//= H Gx; apply/IHx/IHn. 
by move=>z; rewrite inE; case/orP=>[/eqP ->|/Gx].
Qed.

Lemma subset_dfs_dom g n v x :
        {subset v <= dom g} ->
        {subset dfs g n v x <= dom g}.
Proof.
case: n=>[|n] H /=; case: ifP=>//=.
case Dx : (x \in dom g)=>//= _; apply: subset_foldl_dfs_dom.
by move=>z; rewrite inE; case/orP=>[/eqP ->|/H].
Qed.

Lemma uniq_dfs_foldl g n v x : 
        uniq v -> 
        uniq (foldl (dfs g n) v x).
Proof.
elim: n x v=>[|n IHn]; elim=>[|x xs IHx] v U //=; apply: IHx.
- by rewrite if_same.
case: (x \in dom g)=>//=; case: ifP=>// Xv.
by rewrite IHn //= Xv.
Qed.

Lemma uniq_dfs g n v x :
        uniq v ->
        uniq (dfs g n v x).
Proof.
case: n=>[|n] U /=; first by rewrite if_same.
case: (x \in dom g)=>//=; case: ifP=>// Xv.
by rewrite uniq_dfs_foldl //= Xv.
Qed.

(* there's a path in g from x to y avoiding v *)
Inductive dfs_path g (v : seq node) x y : Prop :=
  DfsPath xs of 
    path (edge g) x xs & 
    y = last x xs & 
    disjoint v (x :: xs).

Lemma dfs_path_id g v x :
        x \notin v -> 
        dfs_path g v x x.
Proof.
move=>Vx; apply: (DfsPath (xs:=[::]))=>//=.
by rewrite disjoint1R.
Qed.

Lemma dfs_pathP g n x y v :
        size (dom g) <= size v + n ->
        uniq v ->
        {subset v <= dom g} ->
        y \notin v ->
        x \in dom g ->
        reflect (dfs_path g v x y) (y \in dfs g n v x).
Proof.
elim: n=>[|n IHn] /= in x y v * => Hv Uv Sv Ny Dx. 
- rewrite addn0 in Hv; rewrite Dx if_same (negbTE Ny).
  apply: ReflectF; case=>xs E _; rewrite disjoint_consR.
  by rewrite (uniq_min_size Uv Sv Hv) Dx.
rewrite Dx /=; have [Vx|Vx] := ifPn. 
- by rewrite (negbTE Ny); apply: ReflectF=>[[xs]]; rewrite disjoint_consR Vx.
set v1 := x :: v; set a := children g x; have [->|/eqP Nyx] := eqVneq y x.
- by rewrite subset_dfs ?inE ?eqxx //; apply/ReflectT/dfs_path_id.
apply: (@equivP (exists2 x1, x1 \in a & dfs_path g v1 x1 y))=>/=; last first. 
- split=>{IHn} [[x1 Hx1 [p1 P1 E1 D1]]|[p /shortenP []]]. 
  - apply: (DfsPath (xs:=x1::p1))=>//=; first by rewrite edge_children -/a Hx1.
    by rewrite disjoint_consR Vx (disjoint_consLE D1).
  case=>[_ _ _ /Nyx|] //= x1 xs /andP [Hx1 Hp1] /and3P [N1 _ _] S1 E1 D1. 
  exists x1=>//; apply: (DfsPath (xs:=xs))=>//; rewrite disjoint_consL N1.
  by rewrite (disjoint_consRE (disjoint_subL (subset_consLR S1) D1)).
move: (Dx).
have {Nyx Ny} : y \notin v1 by apply/norP; move/eqP: Nyx.
have {Sv Dx} : {subset v1 <= dom g} by apply: subset_consLI.
have {Vx Uv} : uniq v1 by rewrite /= Vx.
have {Hv} : size (dom g) <= size v1 + n by rewrite addSnnS.
have : {subset a <= dom g} by apply: childrenD.
elim: {x v}a (x) v1=>[|x xs IHa] x' v /= Dxs Hv U Sv Nv Dx'. 
- by rewrite (negbTE Nv); apply: ReflectF; case.
have Dx : x \in dom g by apply: Dxs; rewrite inE eqxx. 
have Da : {subset xs <= dom g} by move=>z Z; apply/Dxs/subset_consR.
set v2 := dfs g n v x.
have Sv2 : {subset v <= v2} := @subset_dfs g n v [:: x].
have [Hy2|Ny2] := boolP (y \in v2).
- rewrite subset_dfs //; apply: ReflectT. 
  by exists x; [rewrite inE eq_refl|apply/IHn].
apply: {IHa} (equivP (IHa _ _ _ _ _ _ Ny2 Dx))=>//.
- by rewrite (leq_trans Hv) ?leq_add2r ?uniq_leq_size.
- by rewrite uniq_dfs.
- by apply: subset_dfs_dom.
split=>[][x1 Hx1 [p1 P1 Ey D1]].
- exists x1; first by rewrite inE Hx1 orbT.
  by apply: DfsPath (disjoint_subR Sv2 D1).
have Nx1 : x1 \notin v by rewrite (disjoint_consRE D1).
suff D2 : disjoint v2 (x1 :: p1).
- move: Hx1; rewrite inE; case/orP=>[/eqP ?|Hx1]; last first.
  - by exists x1=>//; apply: DfsPath D2.
  subst x1; have : x \notin v2 by rewrite (disjoint_consRE D2).
  by move/negP; elim; apply/IHn=>//; apply: dfs_path_id. 
apply: contraR Ny2=>/disjointN [/= x2 Hx2v Hx2].
case/splitPl: Hx2 Ey P1 D1=>/= pl pr Ex2.
rewrite last_cat cat_path -cat_cons lastI cat_rcons {}Ex2.
move=>Ey /andP [_ P1]; rewrite disjoint_catR=>/andP [D1 D2].
have Nx2 : x2 \notin v by rewrite (disjoint_consRE D2). 
have [p P E D] := IHn _ _ v Hv U Sv Nx2 Dx Hx2v.
apply/IHn=>//; exists (p ++ pr).
- by rewrite cat_path P -E P1.
- by rewrite last_cat -E.
by rewrite -cat_cons disjoint_catR D (disjoint_consRE D2).
Qed.

(******************)
(* Connectivity   *)
(* (reachability) *)
(******************)

(* start dfs with p as avoidance set, then filter out p. *)
(* this computes only the nodes visited during dfs. *)
(* not for client use, hence primed name *)
Definition component' (p : pred node) g x : seq node := 
  filter (predC p) (dfs g (size (dom g)) (filter p (dom g)) x).

(* y is connected from x if y is visited during dfs *)
(* avoiding nodes from p; assuming x in dom g *) 
Definition connect p (g : pregraph) x : pred node := 
  fun y => (x \in dom g) && (y \in component' p g x). 

(* connect lemmas *)

Lemma connectP (p : pred node) (g : pregraph) x y :
        reflect [/\ x \in dom g, ~~ p x & exists xs, 
          [/\ path (edge g) x xs, y = last x xs &
              {in xs, forall z, ~~ p z}]]
          (y \in connect p g x).
Proof. 
rewrite /connect/component'/= {2}/in_mem /= mem_filter /= andbA.
case: (boolP (x \in dom g))=>Dx; last by constructor; case.
case: (boolP (p y))=>Py.
- constructor; case=>_ Px [xs][P E Pxs].
  suff : ~~ p y by rewrite Py.
  have : y \in x :: xs by rewrite E mem_last.
  by rewrite inE=>/orP [/eqP ->|/Pxs]. 
apply: (iffP (dfs_pathP _ _ _ _ _))=>//.
- by rewrite leq_addl.
- by rewrite filter_uniq.
- by move=>z; rewrite mem_filter=>/andP [].
- by rewrite mem_filter negb_and Py.
- case=>xs P E /disjoint_consRE [].
  rewrite mem_filter Dx andbT => Px D.
  split=>//; exists xs; split=>// z Xz; move: (allP D z Xz).
  by rewrite mem_filter (path_dom P Xz) andbT.
case=>_ Px [xs][P E Pxs]; exists xs=>//.
rewrite disjoint_consR mem_filter negb_and Px /=.
by apply/allP=>z /Pxs; rewrite mem_filter negb_and=>->.
Qed. 

(* there's path from x to y iff *)
(* there's path that doesn't loop through x *)
Lemma connectX (p : pred node) (g : pregraph) x y :
        reflect [/\ x \in dom g, ~~ p x & exists xs, 
          [/\ path (edge g) x xs, y = last x xs, 
              x \notin xs &
              {in xs, forall z, ~~ p z}]]
          (y \in connect p g x).
Proof.
case: connectP=>H; constructor; last first.
- case=>Dx Hx [xs][Px Ey Nx Hxs].
  by apply: H; split=>//; exists xs.
case: H=>Dx Hx [xs][Px Ey Hxs]; split=>//.
(* if x doesn't appear in the path xs, then done *)
have [Mx|Nx] := boolP (x \in xs); last by exists xs.
(* path xs loops to x; find the last occurrence of x *)
(* and use the part of the path from that occurrence *)
case: {-1} _ _ _ / (splitLastP Mx) (erefl xs)=>/= {Mx} p1 p2 Nxp2 E. 
rewrite {xs}E /= in Px Ey Hxs. 
rewrite last_cat cat_path rcons_path last_rcons -andbA in Px Ey Hxs.
case/and3P: Px=>Px Ex Pp2; exists p2; split=>//.
by move=>z Z; rewrite Hxs // mem_cat Z orbT.
Qed.

Lemma connect_undef p x : connect p undef x =i pred0.
Proof. by move=>y; apply/connectP; case; rewrite dom_undef. Qed.

Lemma connect_unit p x : connect p Unit x =i pred0.
Proof. by move=>y; apply/connectP; case; rewrite dom0. Qed.

Lemma connectDx p g x y : 
        y \in connect p g x ->
        (x \in dom g) * ~~ p x.
Proof. by case/connectP. Qed.

Lemma connectDy p g x y : 
        y \in connect p g x -> 
        (y \in dom g) * ~~ p y.
Proof.
case/connectP=>Dx Px [xs][P E Pxs].
have : y \in x :: xs by rewrite E mem_last.
rewrite inE; case/orP=>[/eqP ->|Dy].
- by rewrite Dx Px.
by rewrite (path_dom P) // Pxs.
Qed.

Lemma connectD p g x y : 
        y \in connect p g x ->
        (x \in dom g) * (y \in dom g).
Proof. by move=>C; rewrite (connectDx C) (connectDy C). Qed.

Lemma connectDp p g x y : 
        y \in connect p g x ->
        (~~ p x) * (~~ p y).
Proof. by move=>C; rewrite (connectDx C) (connectDy C). Qed.

Lemma connectDN p g x : 
        x \notin dom g -> 
        connect p g x =i pred0.
Proof.
move=>Dx y; apply/negP=>/connectD [].  
by rewrite (negbTE Dx).
Qed.

Lemma connectDNp (p : pred node) g x : 
        p x -> 
        connect p g x =i pred0.
Proof.
move=>Hx y; apply/negP=>/connectX [].
by rewrite Hx.
Qed.

Lemma connect0 p g x :
        x \in connect p g x = (x \in dom g) && ~~ p x.
Proof. by apply/connectP/andP; case=>// H1 H2; split=>//; exists [::]. Qed.

Lemma connect0I (p : pred node) (g : pregraph) x :
        x \in dom g ->
        ~~ p x ->
        x \in connect p g x.
Proof. by rewrite connect0=>->->. Qed.

Lemma connect0N (p : pred node) (g : pregraph) x y : 
        x \in dom g -> 
        ~~ p x ->
        y \notin connect p g x ->
        x != y.
Proof. by move=>Gx Px; apply: contra=>/eqP <-; rewrite connect0 Gx. Qed.

Lemma connect_trans p g : transitive (connect p g).
Proof.
move=>x y z /connectP [Dy Hy][ys][Py Ey Hys].
case/connectP=>Dx Hx [xs][Px Ex Hxs].
apply/connectP; split=>//.
exists (ys ++ xs); split=>[||w].
- by rewrite cat_path -Ey Py Px. 
- by rewrite last_cat -Ey.
by rewrite mem_cat; case/orP; [apply: Hys|apply: Hxs].
Qed.

Lemma connectUnL p g1 g2 x :
        valid (g1 \+ g2) ->
        {subset connect p g1 x <= 
                connect p (g1 \+ g2) x}.
Proof.
move=>V y /connectP [Dx Hx][xs][Px Ey Hxs]. 
apply/connectP; split=>//; first by rewrite domUn inE V Dx.
exists xs; split=>//.
by apply: sub_path Px=>z w; apply: edgeUnL V.
Qed.

Lemma connectUnR p g1 g2 x :
        valid (g1 \+ g2) ->
        {subset connect p g2 x <= 
                connect p (g1 \+ g2) x}.
Proof. by rewrite joinC; apply: connectUnL. Qed.

Lemma connectUn p g1 g2 x : 
        [pcm g1 <= g2] ->
        valid g2 ->
        {subset connect p g1 x <= connect p g2 x}.
Proof. by case=>g ->; apply: connectUnL. Qed.

Lemma connect_avoid_graph g p x :
        connect p g x =i 
        connect (predU p (predC (mem (dom g)))) g x.
Proof.
move=>y; apply/connectP/connectP; last first.
- case=>Dx; rewrite !inE negb_or Dx andbT=>Hx [xs][Px Ey Hxs].
  split=>//; exists xs; split=>// z /Hxs.  
  by rewrite !inE negb_or; case/andP.
case=>Dx Hx [xs][Px Ey Hxs]; split=>//.
- by rewrite !inE negb_or Hx Dx.
exists xs; split=>// z Z; rewrite !inE negb_or Hxs //= negbK.
by apply: path_dom Px _ Z.
Qed.

Lemma connect_umfiltk g p x : 
        connect p (um_filterk (predC p) g) x =i connect p g x.
Proof.
case: (normalP g)=>[->|V y]; first by rewrite pfundef.
apply/connectP/connectP; case; rewrite dom_umfiltk inE /=.
- case/andP=>Hx Dx _ [xs][Px Ey Hxs]; split=>//. 
  exists xs; rewrite -(eq_in_path (@edge_umfiltkE g p)) //.
  by apply/allP/in_consE.
move=>Dx Hx [xs][Px Ey Hxs]; rewrite Dx Hx; split=>//.
exists xs; rewrite (eq_in_path (@edge_umfiltkE g p)) //. 
by apply/allP/in_consE.
Qed.

Lemma connect_sub g (p1 p2 : pred node) x :
        subpred p2 p1 ->
        {subset connect p1 g x <= connect p2 g x}.
Proof.
move=>S y /connectP [Dx Hx][xs][Px Ey Hxs].
apply/connectP; split=>//; first by apply: contra (S x) Hx. 
by exists xs; split=>// z /Hxs; apply/contra/S.
Qed.

Lemma connect_eq g p1 p2 x :
        p1 =1 p2 ->
        connect p1 g x =i connect p2 g x.
Proof. by move=>S y; apply/idP/idP; apply/connect_sub=>z; rewrite S. Qed.

(* relativized versions of connect_sub and connect_eq *)
(* it suffices to only prove the precondition for nodes in g *)

Lemma connect_in_sub g p1 p2 x :
        {in dom g, subpred p2 p1} ->
        {subset connect p1 g x <= connect p2 g x}.
Proof.
move=>S y; rewrite connect_avoid_graph=>C.
rewrite connect_avoid_graph.
apply: connect_sub C=>z; rewrite !inE -!(orbC (z \notin _)).
by case Dz: (z \in dom g)=>//=; apply: S Dz.
Qed.

Lemma connect_in_eq g p1 p2 x :
        {in dom g, p1 =1 p2} ->
        connect p1 g x =i connect p2 g x.
Proof. 
move=>S y; rewrite [LHS]connect_avoid_graph [RHS]connect_avoid_graph.
apply: connect_eq=>z; rewrite !inE -!(orbC (z \notin _)).
by case Dz: (z \in dom g)=>//=; rewrite S.
Qed.

(* deconstructing connecting path from left *)
Lemma edge_connect p g x y :
        y != x ->
        y \in connect p g x -> 
        exists2 z, edge g x z & y \in connect p g z.
Proof.
move/eqP=>Nxy /connectP [Dx H][[|a xs]][/= Px Ey Hxs]; first by move/Nxy: Ey.
case/andP: Px=>Px Pxs; exists a=>//; apply/connectP; split. 
- by rewrite (edgeD Px).
- by apply: Hxs; rewrite inE eqxx.
exists xs; split=>// z Z; apply: Hxs.
by rewrite inE Z orbT.
Qed.

(* deconstructing connecting path from right *)
Lemma connect_edge p g x y :
        y != x ->
        y \in connect p g x -> 
        exists2 z, z \in connect p g x & edge g z y.
Proof.
move/eqP=>Nxy /connectP [Dx H][xs].
case: {xs}(lastP xs)=>[|xs a][/= Px Ey Hxs]; first by move/Nxy: Ey. 
rewrite last_rcons in Ey; rewrite -{a}Ey in Px Hxs.
rewrite rcons_path in Px; case/andP: Px=>Pxs Px.
exists (last x xs)=>//; apply/connectP; split=>//.
exists xs; split=>// z Z; apply: Hxs.
by rewrite mem_rcons inE Z orbT.
Qed.

(* extending connecting path from left *)
Lemma edge_connectI p g x y z : 
        x \in dom g ->
        x \notin p ->
        edge g x y ->
        z \in connect p g y ->
        z \in connect p g x.
Proof.
move=>Dx Hx H /connectP [Dy Hy][ys][Py Ez Hys]. 
apply/connectP; split=>//; exists (y::ys).
split=>[||w] //=; first by rewrite H Py.
by rewrite inE; case/orP=>[/eqP ->|/Hys].
Qed.

(* extending connecting path from right *)
Lemma connect_edgeI p g x y z : 
        y \in connect p g x ->
        edge g y z ->
        z \notin p ->
        z \in connect p g x.
Proof.
case/connectP=>Dx Hx [xs][Px Ey Hxs] H Hz.
apply/connectP; split=>//.
exists (rcons xs z); split=>/=.
- by rewrite rcons_path Px -Ey H.
- by rewrite last_rcons.
by move=>w; rewrite mem_rcons inE; case/orP=>[/eqP ->|/Hxs].
Qed.

(***********************)
(* Connected component *)
(***********************)

(* part of g reachable from x (avoiding nothing) *)
Definition subconnect g x : pregraph := 
  um_filterk (mem (connect pred0 g x)) g.

Lemma edge_subconnect g x y z : 
        edge (subconnect g x) y z = 
        [&& y \in connect pred0 g x, 
            z \in connect pred0 g x & 
            edge g y z].
Proof.
rewrite /edge/children/links/oapp/= find_umfiltk /=.
case: ifP=>// _; case: (find y g)=>[ys|]; last by rewrite andbF.
by rewrite !mem_filter /= dom_umfiltk inE -andbA.
Qed.

(* connectivity relation out of x in a connected subcomponent *)
(* is that same connectivity relation out of x in the graph *)
Lemma connect_subconnect g x : 
        connect pred0 (subconnect g x) x =i 
        connect pred0 g x.
Proof.
move=>w; apply/iffE; split; case/connectP. 
- rewrite dom_umfiltk=>/andP [Cx /= Dx] _ [xs][Px Ew _].
  apply/connectP; split=>//; exists xs; split=>//.
  by apply/sub_path/Px=>y z; rewrite edge_subconnect=>/and3P [].
move=>Dx _ [xs][Px Ew _]; apply/connectP; split=>//.
- by rewrite dom_umfiltk inE topredE connect0 Dx.
exists xs; split=>//.
apply/(sub_in_path (P:=[in connect pred0 g x]))/Px.  
- by move=>y z Cy Cz E; rewrite edge_subconnect Cy Cz E.
apply/allP=>z; rewrite inE; case/orP=>[/eqP ->|Hz].
- by rewrite connect0 Dx. 
case/splitPr: Hz Px=>xs1 xs2.
rewrite -cat1s catA cats1 cat_path=>/andP [Px _].
apply/connectP; split=>//.
by exists (rcons xs1 z); rewrite last_rcons.
Qed.

(****************************)
(* Avoidance sets (marking) *)
(****************************)

(* deconstructing connecting path from left *)
(* strenghtening avoidance *)
Lemma edge_connectX p g (x y : node) :
        y != x ->
        y \in connect p g x ->
        exists2 z, 
          edge g x z & y \in connect (predU (pred1 x) p) g z.
Proof.
move/eqP=>Nxy /connectX [Dx Hx][[|a xs]] /= [Px Ey Nx Hxs].
- by move/Nxy: Ey.
case/andP: Px=>Exa Pa; exists a=>//; apply/connectP; split.
- by rewrite (edgeD Exa).
- rewrite !inE negb_or Hxs ?inE ?eqxx // andbT.
  by case: (a =P x) Nx=>//= ->; rewrite inE eqxx. 
exists xs; split=>// z Z.
rewrite !inE negb_or Hxs ?inE ?Z ?orbT // andbT.
by case: (z =P x) Nx=>// <-; rewrite inE Z orbT.
Qed.

(* extending connecting path from left *)
(* weakening avoidance *)
Lemma edge_connectXI (p : pred node) (g : pregraph) x y z : 
        x \in dom g ->
        ~~ p x ->
        edge g x y ->
        z \in connect (predU (pred1 x) p) g y ->
        z \in connect p g x.
Proof. 
move=>Dx Px Ex /(connect_sub (p2:=p)) H. 
apply: edge_connectI Ex (H _)=>//.
by move=>w W; rewrite inE /= W orbT.
Qed.

(* the right-way lemmas can't be stated usefully *)

(* equivalence variant *)
Lemma edge_connectXE p g x y :
        y \in connect p g x <->
        [/\ x \in dom g, ~~ p x & y = x \/ exists2 z, 
            edge g x z & y \in connect (predU (pred1 x) p) g z]. 
Proof.
split=>[C|[Dx Hx]]; last first.
- case=>[->|[z E C]]; first by rewrite connect0 Dx Hx.  
  by apply: edge_connectXI E C.
rewrite !(connectDx C); split=>//. 
case: (y =P x)=>[->|/eqP Nxy]; first by left.
by right; apply: edge_connectX Nxy C.
Qed.

(* if y is reachable from x, but not from x', then *)
(* y is reachable from x by a path that avoids whole *)
(* subcomponent of x' *)
Lemma connect_avoid p g x y x' :
        y \notin connect p g x' ->
        (y \in connect p g x) =
        (y \in connect (predU p [in connect p g x']) g x).
Proof.
move=>Ny; apply/idP/idP; last first.
- by apply: connect_sub=>z Z; rewrite inE Z.
case/connectP=>Dx Hx [xs][Px Ey Hxs]. 
have [Nx|Mx] := boolP (has [in connect p g x'] (x :: xs)); last first.
(* if path contains no nodes reachable from x', nothing to do *)
- move/hasPn: Mx=>Mx; apply/connectP; split=>//.
  - by rewrite inE negb_or Hx Mx // inE eqxx.
  by exists xs; split=>// z Z; rewrite inE negb_or Hxs // Mx // inE Z orbT. 
(* if path contains node reachable from x' *)
(* let a be the last such node in the path *)
case: {-1} _ _ _ / (split_findlast Nx) (erefl (x::xs)).
move=>{Nx} a p1 p2=>Ca /hasPn/= Nx' X.
(* suffices to show that y is reachable from a *)
(* because then y is also reachable from x'; contradiction *)
suff Cy : y \in connect p g a.
- by move: (connect_trans Ca Cy) Ny; rewrite -!topredE /= =>->.
case: p1 X Ey Px Hxs=>[[<- _]|b p1 [_ ->]] /= Ey Px Hxs.
- by apply/connectP; split=>//; exists xs.
rewrite cat_path last_cat last_rcons rcons_path -andbA in Ey Px.
case/and3P: Px=>Px Ea P2; apply/connectP; rewrite !(connectDy Ca); split=>//.
by exists p2; split=>// z Z; rewrite Hxs // mem_cat Z orbT. 
Qed.

Lemma connect_avoid1 p g x y x' :
        y \notin connect p g x' ->
        (y \in connect p g x) = (y \in connect (predU (pred1 x') p) g x).
Proof. 
move=>C; apply/idP/idP; last first.
- by apply: connect_sub=>z Z; rewrite inE Z orbT.
rewrite (connect_avoid _ C); apply/connect_in_sub=>z Dz.
by rewrite !inE=>/orP [/eqP <-|->//]; rewrite connect0 Dz orbN.
Qed.

(******************)
(* Biconnectivity *)
(******************)

(* symmetric closure of connectivity *)

(* y is biconnected from x iff *)
(* x and y are mutually connected *)
Definition biconnect p g x : pred node := 
  [pred y | (x \in connect p g y) && (y \in connect p g x)]. 

Lemma biconnect0 p g x : 
        x \in dom g -> 
        ~~ p x -> 
        biconnect p g x x.
Proof.  by move=>Dx Hp; rewrite /biconnect/= connect0 Dx Hp. Qed.

Lemma biconnectUnL p g1 g2 x y :
        valid (g1 \+ g2) ->
        biconnect p g1 x y -> 
        biconnect p (g1 \+ g2) x y.
Proof. by move=>V /andP [Cx Cy]; apply/andP; split; apply/connectUnL. Qed.

Lemma biconnectUnR p g1 g2 x y :
        valid (g1 \+ g2) ->
        biconnect p g2 x y -> 
        biconnect p (g1 \+ g2) x y.
Proof. by rewrite joinC; apply: biconnectUnL. Qed.

Lemma biconnect_sub g (p1 p2 : pred node) (x : node) :
        subpred p2 p1 -> 
        {subset biconnect p1 g x <= biconnect p2 g x}.
Proof. 
by move=>S y; rewrite !inE=>/andP [Hx Hy]; rewrite !(connect_sub S). 
Qed.

Lemma biconnect_eq g (p1 p2 : pred node) (x : node) :
        p1 =1 p2 -> 
        biconnect p1 g x =i biconnect p2 g x.
Proof. by move=>S y; rewrite !inE !(connect_eq g _ S). Qed.

(**********)
(* Cycles *)
(**********)

(* elements in a cycle are interconnected *)
(* avoiding everything outside the cycle *)

Lemma connect_cycle g xs : 
        cycle (edge g) xs -> 
        {in xs &, forall x y, y \in connect [predC xs] g x}.
Proof.
move=>C x y /rot_to [i q Hr]; rewrite -(mem_rot i) Hr => Hy.
have Hx : x \in xs by rewrite -(mem_rot i) Hr inE eqxx.
have /= Hp1: cycle (edge g) (x :: q) by rewrite -Hr rot_cycle. 
have Dx : x \in dom g.
- by move: Hp1; rewrite rcons_path=>/andP [_ /edgeD][].
case/splitPl: Hy Hp1 Hr=>r s Ey.
rewrite rcons_cat cat_path=>/andP [Hxr].
rewrite Ey rcons_path; case/andP=>Hlx /= Ex Hr.
apply/connectP; split=>//=; first by rewrite negbK.
exists r; split=>// z Z.
by rewrite negbK -(mem_rot i) Hr inE mem_cat Z orbT.
Qed.

Lemma connect_cycle0 g xs : 
        cycle (edge g) xs -> 
        {in xs &, forall x y, y \in connect pred0 g x}.
Proof. by move=>C x y Hx /(connect_cycle C Hx); apply: connect_sub. Qed.

(* elements in a cycle are bi-interconnected *)
(* avoiding everything outside the cycle *)

Lemma biconnect_cycle g xs : 
        cycle (edge g) xs ->
        {in xs &, forall x y, y \in biconnect [predC xs] g x}.
Proof. by move=>C x y Hx Hy; rewrite /biconnect inE !(connect_cycle C). Qed.

Lemma biconnect_cycle0 g xs : 
        cycle (edge g) xs ->
        {in xs &, forall x y, y \in biconnect pred0 g x}.
Proof. by move=>C x y Hx /(biconnect_cycle C Hx); apply: biconnect_sub. Qed.

Lemma biconnect_cycle2P p g x y : 
        x != y ->
        reflect (exists xs : seq node, 
                   [/\ y \in xs, cycle (edge g) (x :: xs) &
                       {in x :: xs, forall z : node, ~~ p z}])
                (y \in biconnect p g x).
Proof.
move=>Nxy; apply/(iffP idP)=>[|[ys][Py Cy Hys]]; last first.
- apply: biconnect_sub (biconnect_cycle Cy _ _).
  - by move=>z; apply/contraL/Hys.
  - by rewrite inE eqxx. 
  by rewrite inE Py orbT.
case/andP=>/connectP [Dy Hy][ys]; elim/last_ind: ys Nxy=>[|ys a IH] Nxy.
- by move/eqP: Nxy=>Nxy [_ /Nxy].
rewrite rcons_path last_rcons; case=>/[swap] <-{a} /andP [Py Ex Hys].
case/connectP=>Dx Hx [xs][Px Ey Hxs]; exists (xs ++ ys); split=>/=. 
- have := mem_last x xs.
  by rewrite -Ey inE eq_sym (negbTE Nxy) /= mem_cat=>->.
- by rewrite rcons_path cat_path last_cat -Ey Px Py Ex.
by move=>z; rewrite -mem_rcons rcons_cat mem_cat=>/orP [];
[apply: Hxs|apply: Hys].
Qed.

Lemma biconnect_cycle2P0 g x y : 
        x != y ->
        reflect (exists2 xs, y \in xs & cycle (edge g) (x :: xs)) 
                (y \in biconnect pred0 g x).
Proof.
move=>Nxy; apply/(iffP (biconnect_cycle2P pred0 g Nxy)).
- by case=>xs [H1 H2 H3]; exists xs.
by case=>xs H1 H2; exists xs.
Qed.

(**************)
(* Acyclicity *)
(**************)

(* graph is preacyclic if only self-loops are biconnected *)
Definition preacyclic g := 
  all2rel (fun x y => (y \in biconnect pred0 g x) ==> (x == y)) (dom g).

(* graph is acyclic if it doesn't even have self-loops *)
Definition acyclic g := 
  preacyclic g && all (fun x => ~~ edge g x x) (dom g).

Lemma preacyclicP g : 
        reflect {in dom g &, forall x y, y \in biconnect pred0 g x -> x = y}
                (preacyclic g).
Proof.
apply: (iffP idP)=>[|H].
- by move/allrelP=>H x y Dx Dy C; apply/eqP/(implyP _ C)/H. 
by apply/allrelP=>x y Dx Dy; apply/implyP=>K; apply/eqP/H.
Qed.

Lemma preacyclicL g1 g2 :
        valid (g1 \+ g2) ->
        preacyclic (g1 \+ g2) -> 
        preacyclic g1.
Proof.
move=>V /preacyclicP H.
apply/preacyclicP=>x y Dx Dy C; apply: H.
- by rewrite domUn inE V Dx.
- by rewrite domUn inE V Dy.
by apply: biconnectUnL V C.
Qed.

Lemma preacyclicR g1 g2 :
        valid (g1 \+ g2) ->
        preacyclic (g1 \+ g2) -> 
        preacyclic g2.
Proof. by rewrite joinC; apply: preacyclicL. Qed.

Lemma acyclicL g1 g2 :
        valid (g1 \+ g2) ->
        acyclic (g1 \+ g2) -> 
        acyclic g1.
Proof.
move=>V /andP [Hp /allP Ha].
apply/andP; split; first by apply: preacyclicL Hp.
apply/allP=>x Dx; apply: contra (edgeUnL V) (Ha x _).
by rewrite domUn inE V Dx.
Qed.

Lemma acyclicR g1 g2 :
        valid (g1 \+ g2) ->
        acyclic (g1 \+ g2) -> 
        acyclic g2.
Proof. by rewrite joinC; apply: acyclicL. Qed.

(* graph is acyclic = graph has no cycles *)
Lemma acyclic_cycleP g :
        reflect (forall x xs, x \in dom g -> ~~ cycle (edge g) (x :: xs))
                (acyclic g).
Proof.
apply: (iffP idP)=>[|H]; last first.
- apply/andP; split; last first.
  - by apply/allP=>x Dx; apply: contra (H _ [::] Dx); rewrite /= =>->.
  apply/preacyclicP=>x y Dx Dy By; apply/eqP/(contraLR _ By)=>{By} Nxy.
  by apply/(biconnect_cycle2P0 _ Nxy); case=>/= xs Hx; apply/negP/H/Dx.
case/andP=>/preacyclicP Ng /allP Ne x xs Dx /=.
rewrite rcons_path; apply/negP=>/andP [].
case: xs=>[_|y xs /= /andP [Exy Px]]; first by apply/negP/Ne.
have Dy : y \in dom g by rewrite (edgeD Exy).
have : y \notin biconnect pred0 g x.
- by apply: contraL Exy=>/(Ng x y Dx Dy) <-; apply: Ne Dx.
apply: contraNnot=>Ex; apply: (biconnect_cycle0 (xs:=x::y::xs))=>/=.
- by rewrite Exy rcons_path Px Ex.
- by rewrite inE eqxx.
by rewrite !inE eqxx orbT.
Qed.

Lemma acyclic_links g x :
        acyclic g ->
        x \notin links g x.
Proof.
case/andP=>_ /allP H.
have [Dx|Nx] := boolP (x \in dom g); last by rewrite linksND.
by apply: contra (H _ Dx)=>Lx; rewrite edge_links Dx Lx.
Qed.

(***************)
(* N-pregraphs *)
(***************)

(* getting the n-th link *)
Definition get_nth g x := nth null (links g x).

Lemma getnth_mem0 g x n :
        (get_nth g x n == null) || 
        (get_nth g x n \in links g x).
Proof.
case: (ltnP n (size (links g x)))=>Hm; last first.
- by rewrite /get_nth nth_default.
by rewrite mem_nth // orbT.
Qed.

Lemma getnth_mem g x n : 
        get_nth g x n != null ->
        get_nth g x n \in links g x.
Proof. by move=>H; move: (getnth_mem0 g x n); rewrite (negbTE H). Qed.

(* n-pregraph is pregraph with global bound n *)
(* for the number of links of a node *)

Definition n_pregraph_axiom (n : nat) (g : pregraph) :=
  {in dom g, forall x, size (links g x) = n}.

Lemma npregraphP n g : 
        n_pregraph_axiom n g <->
        {in range g, forall xs, size xs = n}.
Proof.
split=>H x; last by move=>Dx; apply: H (range_links Dx).
by case/mem_rangeX=>k X; rewrite (In_graph X); apply: H (In_dom X).
Qed.

Lemma npregraphUnL n g1 g2 :
        valid (g1 \+ g2) ->
        n_pregraph_axiom n (g1 \+ g2) -> 
        n_pregraph_axiom n g1.
Proof. 
by rewrite !npregraphP=>V H x X; apply: H; rewrite rangeUn inE V X.
Qed.

Lemma npregraphUnR n g1 g2 :
        valid (g1 \+ g2) ->
        n_pregraph_axiom n (g1 \+ g2) -> 
        n_pregraph_axiom n g2.
Proof. by rewrite joinC; apply: npregraphUnL. Qed.

Lemma npregraphF n g x : 
        n_pregraph_axiom n g ->
        n_pregraph_axiom n (free g x).
Proof. by rewrite !npregraphP=>H z /rangeF; apply: H. Qed.

Lemma links_nth n g x :
        n_pregraph_axiom n g ->
        x \in dom g ->
        links g x = map (get_nth g x) (iota 0 n).
Proof.
move=>H Dx; apply/(eq_from_nth (x0:=null))=>[|i Hi].
- by rewrite size_map size_iota H.
by rewrite map_nth_iota0 ?H // -(H _ Dx) take_size.
Qed.

(**********)
(**********)
(* Graphs *)
(**********)
(**********)

(* x is in_node if it's in the graph or is null *)
Definition in_node (g : pregraph) (x : node) := 
  (x == null) || (x \in dom g).

(* x is out-node if no edge goes into it *)
Definition out_node (g : pregraph) (x : node) := 
  {in range g, forall xs, x \notin xs}.

(* pregraph is graph if *)
(* all nodes in all adjacency lists are in-nodes *)
Definition graph_axiom (g : pregraph) := 
  forall xs x, xs \in range g -> x \in xs -> in_node g x.

HB.mixin Record isGraph (g : pregraph) := {
  graph_subproof : graph_axiom g}.
#[short(type=graph)]
HB.structure Definition Graph := {g of isGraph g }.

(* removing out-node causes no dangling edges; *)
(* hence preserves graph axiom *)
Lemma graphF g x :
        out_node g x ->
        graph_axiom g ->
        graph_axiom (free g x).
Proof.
move=>Hna Ha xs q /rangeF Hs Hq.
move: (Ha xs q Hs Hq) (Hna _ Hs)=>{}Hs.
rewrite /in_node domF inE in Hs *.
by case: (x =P q) Hq=>//= ->->.
Qed.

(* reachable component of a graph is a graph *)
Lemma graph_subconnect g x :
        valid g ->
        graph_axiom g -> 
        graph_axiom (subconnect g x).
Proof.
have E : g = subconnect g x \+ um_filterk 
  (negb \o connect pred0 g x) g by apply: umfilt_predC.
move=>V Ha xs /= n Hxs Hn; have {}Dn : in_node g n.
- by apply: Ha Hn; rewrite E rangeUn inE -E V Hxs.
case/mem_rangeX: Hxs=>k /In_umfiltX [/= Ck] /In_graph Hf.
rewrite /in_node in Dn *; case/boolP: (n == null) Dn=>//= Hnn Dn.
case: (connectD Ck)=>_ Dk.
rewrite /subconnect dom_umfiltk inE /= Dn andbT.
apply: connect_trans Ck _; apply/connectP; split=>//.
by exists [:: n]; split=>//=; rewrite edge_links Dn -Hf Hn.
Qed.

Lemma graph_links g x y :
        graph_axiom g ->
        y \in links g x ->
        in_node g y.
Proof. by move=>H /[dup]/linksD Dx; apply/H/range_links. Qed.

Lemma graph_children g x y : 
        graph_axiom g ->
        (y \in children g x) = (y != null) && (y \in links g x).
Proof.
move=>H; rewrite mem_filter -!(andbC (y \in links _ _)).
case Ly : (y \in links g x)=>//=.
move/(graph_links H): Ly; rewrite /in_node.
by case: (y =P null)=>//= ->; rewrite cond_dom.
Qed.

Lemma graph_getnth g x n :
        graph_axiom g ->
        in_node g (get_nth g x n).
Proof.
case: (ltnP n (size (links g x)))=>Hm; last first.
- by rewrite /get_nth nth_default.
by move/(graph_links (x:=x)); apply; rewrite mem_nth.
Qed.

