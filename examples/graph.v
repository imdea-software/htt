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
From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype ssrnat seq path.
From pcm Require Import options axioms pred prelude.
From pcm Require Import pcm unionmap natmap autopcm automap.
From pcm Require Import seqext.


(* disjointness and subset stuff *)

Definition disjoint {A : eqType} (s1 s2 : seq A) := 
  all (fun x => x \notin s1) s2.

Arguments disjoint {A} : simpl never.

Lemma disjointC (A : eqType) (s1 s2 : seq A) :
        disjoint s1 s2 = disjoint s2 s1.
Proof. 
apply/idP/idP=>/allP S; apply/allP=>x X; 
by apply/negP=>/S; rewrite X.
Qed.

Lemma disjoint_catR (A : eqType) (s s1 s2 : seq A) : 
        disjoint s (s1 ++ s2) = 
        disjoint s s1 && disjoint s s2.
Proof. by rewrite /disjoint all_cat. Qed.

Lemma disjoint_catL (A : eqType) (s s1 s2 : seq A) : 
        disjoint (s1 ++ s2) s = 
        disjoint s1 s && disjoint s2 s.
Proof. by rewrite -!(disjointC s) disjoint_catR. Qed.

Lemma disjoint1L (A : eqType) x (s : seq A) :
        disjoint [:: x] s = (x \notin s).
Proof.
apply/idP/idP.
- by apply: contraL=>X; apply/allPn; exists x=>//; rewrite negbK inE.
by apply: contraR=>/allPn [y H]; rewrite inE negbK =>/eqP <-.
Qed.

Lemma disjoint1R (A : eqType) x (s : seq A) :
        disjoint s [:: x] = (x \notin s).
Proof. by rewrite disjointC disjoint1L. Qed.

Lemma disjoint_consL (A : eqType) x (s1 s2 : seq A) :
        disjoint (x :: s1) s2 = 
        (x \notin s2) && disjoint s1 s2.
Proof. by rewrite -cat1s disjoint_catL disjoint1L. Qed.

Lemma disjoint_consR (A : eqType) x (s1 s2 : seq A) :
        disjoint s1 (x :: s2) = 
        (x \notin s1) && disjoint s1 s2.
Proof. by rewrite -cat1s disjoint_catR disjoint1R. Qed.

Lemma disjoint_consLI (A : eqType) x (s1 s2 : seq A) :
        x \notin s2 ->
        disjoint s1 s2 ->
        disjoint (x :: s1) s2.
Proof. by rewrite disjoint_consL=>->->. Qed.

Lemma disjoint_consRI (A : eqType) x (s1 s2 : seq A) :
        x \notin s1 ->
        disjoint s1 s2 ->
        disjoint s1 (x :: s2).
Proof. by rewrite disjoint_consR=>->->. Qed.

Lemma disjoint_consLE (A : eqType) x (s1 s2 : seq A) :
        disjoint (x :: s1) s2 ->
        (x \notin s2) * (disjoint s1 s2).
Proof. by rewrite disjoint_consL=>/andX. Qed.

Lemma disjoint_consRE (A : eqType) x (s1 s2 : seq A) :
        disjoint s1 (x :: s2) ->
        (x \notin s1) * (disjoint s1 s2).
Proof. by rewrite disjoint_consR=>/andX. Qed.

Lemma disjoint_subL (A : eqType) (s s1 s2 : seq A) : 
        {subset s2 <= s1} ->
        disjoint s s1 ->
        disjoint s s2.
Proof. by move=>X /allP H; apply/allP=>z /X /H. Qed.

Lemma disjoint_subR (A : eqType) (s s1 s2 : seq A) : 
        {subset s2 <= s1} ->
        disjoint s1 s ->
        disjoint s2 s.
Proof. 
move=>X; rewrite disjointC=>/(disjoint_subL X).
by rewrite disjointC.
Qed.

Lemma disjoint_eqL {A : eqType} {s s1 s2 : seq A} :
        s1 =i s2 ->
        disjoint s1 s = disjoint s2 s.
Proof. by move=>X; apply/idP/idP; apply: disjoint_subR=>z; rewrite X. Qed.

Lemma disjoint_eqR {A : eqType} {s s1 s2 : seq A} :
        s1 =i s2 ->
        disjoint s s1 = disjoint s s2.
Proof. by move=>X; apply/idP/idP; apply: disjoint_subL=>z; rewrite X. Qed.

Lemma disjointN (A : eqType) (s1 s2 : seq A) : 
        ~~ disjoint s1 s2 ->
        exists2 x, x \in s1 & x \in s2.
Proof. by case/allPn=>x; rewrite negbK; exists x. Qed.

Lemma subset_consL (A : eqType) x (s1 s2 : seq A) : 
        {subset x :: s1 <= s2} <->
        x \in s2 /\ {subset s1 <= s2}.
Proof.
split=>[S|[X S]].
- by split=>[|z Z]; apply: S; rewrite inE ?eqxx ?Z ?orbT.
by move=>z; rewrite inE; case/orP=>[/eqP ->|/S//].
Qed.

Lemma subset_consLI (A : eqType) x (s1 s2 : seq A) : 
        x \in s2 ->
        {subset s1 <= s2} ->
        {subset x :: s1 <= s2}.
Proof. by move=>H1 H2; rewrite subset_consL. Qed.

Lemma subset_consR (A : eqType) x (s : seq A) : 
        {subset s <= x :: s}.
Proof. by move=>z E; rewrite inE E orbT. Qed.

Lemma subset_consLR (A : eqType) x (s1 s2 : seq A) : 
        {subset s1 <= s2} ->
        {subset x :: s1 <= x :: s2}.
Proof.
move=>X z; rewrite !inE; case/orP=>[|/X] -> //.
by rewrite orbT.
Qed.

Hint Resolve subset_consR : core.

Lemma subset_refl (A : Type) (s : pred A) : 
        {subset s <= s}.
Proof. by []. Qed.

Lemma subset_trans (A : eqType) (s1 s2 s3 : pred A) :
        {subset s1 <= s2} ->
        {subset s2 <= s3} ->
        {subset s1 <= s3}. 
Proof. by move=>S1 S2 z /S1/S2. Qed.




(* Pregraphs are natmaps, mapping nodes into *)
(* seq node listing the children of the node (adjacency list) *)
(* Technically pregraph's a "prequiver", because this representation *)
(* allows loops and parallel edges *)
(* Pregraph differs from graph, in that edges can *dangle*; that is *)
(* originate or terminate (or both) with a node that isn't in the graph *)

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
  Mem_UmMap_PredType pregraph.
Coercion Pred_of_history (x : pregraph) : Pred_Class := 
  [eta Mem_UmMap x].

Notation "x &-> v" := (ptsT pregraph x v) (at level 30).

(* x is out-node if no edge goes into it *)
Definition out_node (g : pregraph) (x : node) := 
  all (fun s => x \notin s) (range g).

(* pregraph is graph if valid, and *)
(* all nodes in all adjacency lists are good *)
Definition graph_axiom (g : pregraph) := 
  valid g && all (all (fun x : node => (x == null) || (x \in dom g))) (range g). 

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
move/allP=>/= Hna /andP [V /allP/= Ha].
rewrite /graph_axiom validF V /=.
apply/allP=>/= s /rangeF Hs; apply/allP=>q Hq.
move/allP: (Ha _ Hs) (Hna _ Hs)=>/(_ _ Hq) {}Hs. 
by rewrite domF inE; case: (x =P q) Hq=>//= ->->.
Qed.

(* children of node x obtained by non-dangingle edges *)
Definition children (g : pregraph) x : seq node :=
  oapp (filter (mem (dom g))) [::] (find x g).

Lemma children_undef x : children undef x = [::].
Proof. by []. Qed.

Lemma children_unit x : children Unit x = [::].
Proof. by []. Qed.

Lemma childrenND g x :
        x \notin dom g ->
        children g x = [::].
Proof. by rewrite /children/oapp; case: dom_find. Qed.

Lemma childrenD g x : 
        {subset children g x <= dom g}.
Proof.
move=>y; rewrite /children/oapp/=.
case D : (find x g)=>[a|//].
by rewrite mem_filter; case/andP.
Qed.

Lemma childrenUnL g1 g2 x : 
        valid (g1 \+ g2) ->
        {subset children g1 x <= children (g1 \+ g2) x}.
Proof.
move=>V y; rewrite /children/oapp findUnL //.
case: dom_find=>// ys /In_find/In_dom /= D _.
rewrite !mem_filter /= domUn inE V /=.
by case/andP=>->->.
Qed.

Lemma childrenUnR g1 g2 x : 
        valid (g1 \+ g2) ->
        {subset children g2 x <= children (g1 \+ g2) x}.
Proof. by rewrite joinC; apply: childrenUnL. Qed.

(* edge relation is just the applicative variant of children *)
(* thus, consider removing one of them *)

Definition edge g : rel node := mem \o children g.
Arguments edge g x y : simpl never.

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

Lemma edge_dom g x y : 
        edge g x y -> 
        (x \in dom g) * (y \in dom g).
Proof.
rewrite /edge/= => H; split; last by apply: childrenD H. 
by apply: contraLR H=>/childrenND ->.
Qed.

Lemma find_edge g x y ys :
        find x g = Some ys ->
        edge g x y = (y \in dom g) && (y \in ys).
Proof.
rewrite /edge/children/oapp/= => ->.
by rewrite mem_filter.
Qed.

Lemma path_dom g x xs :
        path (edge g) x xs ->
        {subset xs <= dom g}.
Proof.
elim: xs x=>[|a xs IH] x //= /andP [/edge_dom [_ He] /IH].
by apply: subset_consLI He. 
Qed.

(* lifting the theory of finite graphs to unbounded pregraphs *)

(* list of nodes traversed by depth-first search of g  *)
(* at depth n, starting from x, and avoiding v *)
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
- rewrite addn0 in Hv; case: (uniq_min_size Uv Sv Hv) Ny=>_ Ev /negbTE Ny.
  suff: ~ dfs_path g v x y by rewrite Dx if_same Ny; apply: ReflectF.
  by case=>xs E _; rewrite disjoint_consR Ev Dx.
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
have Da : {subset xs <= dom g} by apply/subset_trans/Dxs/subset_consR.
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

(* start dfs with p as avoidance set, then filter out p. *)
(* this computes only the nodes visited during dfs. *)
(* not for client use, hence primed name *)
Definition component' (p : pred node) g x : seq node := 
  filter (predC p) (dfs g (size (dom g)) (filter p (dom g)) x).

(* y is connected from x if y is visited during dfs *)
(* under assumption that x is in dom g *)
Definition connect p (g : pregraph) := 
  [rel x y | (x \in dom g) && (y \in component' p g x)].

Lemma connectP p (g : pregraph) x y :
        reflect [/\ x \in dom g, ~~ p x & exists xs, 
          [/\ path (edge g) x xs, y = last x xs &
              {in xs, forall z, ~~ p z}]]
          (y \in connect p g x).
Proof.
rewrite /connect/component' inE mem_filter /= andbA.
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

Lemma connectX p g x y : 
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

Lemma connectXN (p : pred node) g x : 
        p x -> 
        connect p g x =i pred0.
Proof.
move=>Hx y; apply/negP=>/connectX [].
by rewrite Hx.
Qed.

Lemma connect0 p g x :
        x \in connect p g x = (x \in dom g) && ~~ p x.
Proof. by apply/connectP/andP; case=>// H1 H2; split=>//; exists [::]. Qed.

Lemma connect0I p g x :
        x \in dom g ->
        ~~ p x ->
        x \in connect p g x.
Proof. by rewrite connect0=>->->. Qed.

Lemma connect0N p g x y : 
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

Lemma connect_sub g p1 p2 x :
        {subset p2 <= p1} ->
        {subset connect p1 g x <= connect p2 g x}.
Proof.
move=>S y /connectP [Dx Hx][xs][Px Ey Hxs].
apply/connectP; split=>//; first by apply: contra (S x) Hx. 
by exists xs; split=>// z /Hxs; apply/contra/S.
Qed.

(* exteding connecting path from left *)
Lemma edge_connectI p g x y z : 
        x \in dom g ->
        ~~ p x ->
        edge g x y ->
        z \in connect p g y ->
        z \in connect p g x.
Proof.
move=>Dx Hx H /connectP [Dy Hy][ys][Py Ez Hys]. 
apply/connectP; split=>//; exists (y::ys).
split=>[||w] //=; first by rewrite H Py.
by rewrite inE; case/orP=>[/eqP ->|/Hys].
Qed.

(* exteding connecting path from right *)
Lemma connect_edgeI p g x y z : 
        y \in connect p g x ->
        edge g y z ->
        ~~ p z ->
        z \in connect p g x.
Proof.
case/connectP=>Dx Hx [xs][Px Ey Hxs] H Hz.
apply/connectP; split=>//.
exists (rcons xs z); split=>/=.
- by rewrite rcons_path Px -Ey H.
- by rewrite last_rcons.
by move=>w; rewrite mem_rcons inE; case/orP=>[/eqP ->|/Hxs].
Qed.

(* destructing connecting path from left *)
Lemma edge_connectE p g x y :
        y \in connect p g x -> 
        y = x \/ 
        exists2 z, edge g x z & y \in connect p g z.
Proof.
case/connectP=>Dx H [[|a xs]][/= Px Ey Hxs]; first by left.
right; case/andP: Px=>Px Pxs; exists a=>//.
apply/connectP; split. 
- by rewrite (edge_dom Px).
- by apply: Hxs; rewrite inE eqxx.
exists xs; split=>// z Z; apply: Hxs.
by rewrite inE Z orbT.
Qed.

(* deconstructing connecting path from right *)
Lemma connect_edgeE p g x y :
        y \in connect p g x -> 
        y = x \/ 
        exists2 z, z \in connect p g x & edge g z y.
Proof.
case/connectP=>Dx H [xs].
case: {xs}(lastP xs)=>[|xs a][/= Px Ey Hxs]; first by left.
right; rewrite last_rcons in Ey; rewrite -{a}Ey in Px Hxs.
rewrite rcons_path in Px; case/andP: Px=>Pxs Px.
exists (last x xs)=>//; apply/connectP; split=>//.
exists xs; split=>// z Z; apply: Hxs.
by rewrite mem_rcons inE Z orbT.
Qed.

(* part of g reachable from x (avoiding nothing) *)
Definition subconnect g x : pregraph := 
  um_filterk (connect pred0 g x) g.

(* part of g unreachable from x (avoiding nothing) *)
Definition subdisconnect g x : pregraph := 
  um_filterk (negb \o connect pred0 g x) g.

Lemma connect_split g x : 
        g = subconnect g x \+ subdisconnect g x.
Proof. by apply: umfilt_predC. Qed.

(* reachable component of a graph is a graph *)
Lemma graph_subconnect g x :
        graph_axiom g -> 
        graph_axiom (subconnect g x).
Proof.
have E := connect_split g x.
case/andP=>V Ha; apply/andP; split; first by rewrite pfV. 
apply/allP=>/= xs Hxs; move/allP: Ha=>/(_ xs).
rewrite {1}E rangeUn inE -E V Hxs /= => /(_ erefl) Ha.
case/mem_rangeX: Hxs=>k /In_umfiltX [/= Hk] /In_find Hf.
apply/allP=>n Hn; move/allP: Ha=>/(_ _ Hn).
case/boolP: (n == null)=>//= Hnn.
rewrite /subconnect dom_umfiltk inE /= => En.
rewrite En andbT /=; apply: (connect_trans Hk).
apply/connectP; split=>//=; first by rewrite (connectD Hk).
exists [:: n]; split=>//=.
by rewrite (find_edge _ Hf) En Hn.
Qed.


UP TO HERE







(*******************)


(* TODO generalize to arbitrary boundary? *)
Definition subconnect p g := um_filterk (fun z => z \in connect Unit g p) g.

Definition subdisconnect p g := um_filterk (fun z => z \notin connect Unit g p) g.

Lemma connect_split p g : g = subconnect p g \+ subdisconnect p g.
Proof. by apply: umfilt_predC. Qed.

Lemma good_subconnect p g :
  good_graph g -> good_graph (subconnect p g).
Proof.
have E := connect_split p g.
case/andP=>V Ha; apply/andP; split; first by rewrite valid_umfilt.
apply/allP=>ns Hns; move/allP: Ha=>/(_ ns).
rewrite {1}E rangeUn inE -E V Hns /= => /(_ erefl) Ha.
case/mem_rangeX: Hns=>k; case/In_umfilt=>/= Hk /In_find Hf.
apply/allP=>n Hn; move/allP: Ha=>/(_ _ Hn).
rewrite /good_ptr; case/boolP: (n == null)=>//= Hnn.
rewrite /subconnect dom_umfiltk inE /= =>En; rewrite En andbT.
apply: (connect_trans Hk); apply/connectP.
exists [::n]; split=>//=; last by rewrite !dom0.
by rewrite andbT (find_edge _ Hf) En.
Qed.

Lemma edge_subconnect p g : subrel (edge (subconnect p g)) (edge g).
Proof.
move=>x y; rewrite /edge /links find_umfiltk; case: ifP=>//= Hx.
by case Ef: (find x g)=>[v|] //=; rewrite !mem_filter dom_umfiltk inE /= -andbA; case/andP.
Qed.

Lemma connect_subconnect p g : connect Unit (subconnect p g) p =i connect Unit g p.
Proof.
move=>z; apply/iffE; split.
- case/connectP=>xs [Hxs {z}-> /implyP Nxs _].
  apply/connectP; exists xs; split=>//=; last by rewrite dom0 /= all_predT.
  - by apply/sub_path/Hxs/edge_subconnect.
  by apply/implyP=>/Nxs; rewrite dom_umfiltk inE /=; case/andP.
case/connectP=>xs [Hxs {z}-> /implyP Nxs _].
have Hpd : p \in dom g.
- case: xs Hxs Nxs=>/=; first by move=>_; apply.
  by move=>h t; case/andP; case/edge_dom.
apply/connectP; exists xs; split=>//=; last by rewrite dom0 /= all_predT.
- apply/(sub_in_path (P:=fun q => q \in connect Unit g p))/Hxs.
  - move=>x y; rewrite !inE=>Hx Hy.
    rewrite /edge /links find_umfiltk Hx.
    case Ef: (find x g)=>[v|] //=; rewrite !mem_filter dom_umfiltk inE /= -andbA =>->.
    by rewrite andbT.
  move=>/=; apply/andP; split; first by apply/connect0=>//; rewrite dom0.
  apply/allP=>x Hx; case/splitPr: Hx Hxs Nxs=>xs1 xs2.
  rewrite -cat1s catA cats1 cat_path /=; case/andP=>H1 H2 _.
  apply/connectP; exists (rcons xs1 x); split=>//=.
  - by rewrite last_rcons.
  - by rewrite -cats1 cat_nilp andbF.
  by rewrite dom0 /= all_predT.
apply/implyP=>/Nxs; rewrite dom_umfiltk inE /==>->; rewrite andbT.
by apply/connect0=>//; rewrite dom0.
Qed.

End GraphOps.

Section Marking.

Lemma connectMPtUn p m g x (cs : seq ptr) :
  valid m ->
  p \notin dom m ->
  find p g = Some cs ->
  forall z, z != p ->
             x \in cs -> z \in connect        m  g x ->
  exists2 y, y \in cs &  z \in connect (#p \+ m) g y.
Proof.
move=>Vm Npm Hc z Hzp Hx; case/connectP=>xs [Hp Ez Nxs] Ha.
rewrite {z}Ez in Hzp *.
case Hpxs: (p \in x::xs); last first.
- (* there's no loop, path stays the same *)
  exists x=>//; apply/connectP; exists xs; split=>//.
  apply/allP=>z Hz; rewrite domPtUn inE validPtUn !negb_and negb_or /= negbK Vm (negbTE Npm) /=.
  move/allP: Ha=>/(_ _ Hz) ->; rewrite andbT.
  by apply/negP=>/eqP E; rewrite E Hz in Hpxs.
(* there's at least one loop, find the last p *)
case: {-1}_ _ _ / (splitLastP Hpxs) (erefl (x::xs)) =>{Hpxs} xs1 xs2 Hxs2.
case: xs2 Hxs2=>/=.
- move=>_; rewrite cats0=>E.
  have /=: last x (x :: xs) = last x (rcons xs1 p) by rewrite E.
  by rewrite last_rcons=>{}E; rewrite E eq_refl in Hzp.
move=>ch xs2; rewrite inE negb_or; case/andP => Npch Nxs2 E.
case: xs1 E=>/=.
- (* p links to itself *)
  case=>Exp E2; rewrite {x Nxs}Exp {xs}E2 /= in Hx Hp Ha Hzp *.
  case/andP: Hp=>He Hp.
  exists ch; first by move: He; rewrite (find_edge _ Hc); case/andP.
  apply/connectP; exists xs2; split=>//.
  - by case/edge_dom: He=>_ ->; exact: implybT.
  case/and3P: Ha=>_ Hch Ha.
  apply/allP=>z; rewrite domPtUn inE validPtUn !negb_and negb_or /= negbK Vm (negbTE Npm) /=.
  case/orP=>[/eqP {z}->| Hz]; first by rewrite Npch.
  move/allP: Ha=>/(_ _ Hz) ->; rewrite andbT.
  by apply/negP=>/eqP E; rewrite E Hz in Nxs2.
(* there's a non-trivial path before the loop *)
move=>_ xs1 [_ Exs]; rewrite {xs}Exs in Hp Nxs Ha Hzp *.
move: Hp; rewrite cat_path last_cat !last_rcons rcons_path -andbA /=.
case/and4P=>_ _ He Hp2.
exists ch; first by move: He; rewrite (find_edge _ Hc); case/andP.
apply/connectP; exists xs2; split=>//.
- by case/edge_dom: He=>_ ->; exact: implybT.
move: Ha; rewrite -cat_cons all_cat; case/andP=>_ Ha.
apply/allP=>z Hz; rewrite domPtUn inE validPtUn !negb_and negb_or /= negbK Vm (negbTE Npm) /=.
move/allP: Ha=>/(_ _ Hz) ->; rewrite andbT.
move: Hz; rewrite inE; case/orP=>[/eqP->|Hz] //.
by apply/negP=>/eqP E; rewrite E Hz in Nxs2.
Qed.

Lemma connectMUnSub m1 m2 g x :
  valid (m1 \+ m2) ->
  forall z, z \in connect (m1 \+ m2) g x ->
            z \in connect        m2  g x.
Proof.
move=>Vm z; case/connectP=>xs [Hp Ez Nxs] Ha.
apply/connectP; exists xs; split=>//.
apply/sub_all/Ha=>q; apply: contra.
rewrite domUn inE Vm => ->.
by rewrite orbT.
Qed.

Corollary connectMPtUnHas p m g cs :
  valid m ->
  p \notin dom m ->
  find p g = Some cs ->
  forall z, z \in connect m g p = (z == p) || has (fun x => z \in connect (#p \+ m) g x) cs.
Proof.
move=>Vm Npm Hc z.
rewrite (connect_eq_links Hc) //; case: eqP=>/= // /eqP Hzp.
have Vpm : valid (#p \+ m) by rewrite validPtUn Vm.
apply/iffE; split; case/hasP=>x Hx.
- move=>Hz; apply/hasP.
  by apply: (connectMPtUn (x:=x)).
move/(connectMUnSub Vpm)=>Hz.
by apply/hasP; exists x.
Qed.

Lemma connectMUn p m1 m2 g x c (cs : seq ptr) :
  valid (m2 \+ m1) ->
  find p g = Some cs ->
  c \in cs -> good_ptr g c ->
  dom m2 =i connect m1 g c ->
  forall z,  x \in cs                  -> z \in connect m1 g x ->
  z \in connect m1 g c
  \/
  exists2 y, y \in filter (predC1 c) cs & z \in connect (m2 \+ m1) g y.
Proof.
move=>V21 Hf Hc Hcd Hm z Hxc. case/connectP=>xs [Hp Ez Nxs] Ha.
case/boolP: (all (fun z => z \notin dom m2) (x::xs))=>Hpxs.
- (* path doesn't go through the marked component *)
  right; exists x.
  - rewrite mem_filter Hxc andbT /=.
    case/orP: Hcd=>[/eqP->|Hcd].
    - suff: x \in dom g by move/dom_cond.
      by case: {Ez Ha Hpxs}xs Hp Nxs=>//= h t; case/andP; case/edge_dom.
    apply/negP=>/eqP Exc; move: Hpxs=>/=; case/andP=>+ _; rewrite Exc Hm.
    move/negP; apply; apply: connect0=>//.
    by move: Ha=>/=; case/andP=>+ _; rewrite Exc.
  apply/connectP; exists xs; split=>//.
  apply/allP=>q Hq; rewrite domUn inE negb_and negb_or V21 /=.
  by move/allP: Ha=>/(_ _ Hq)->; move/allP: Hpxs=>/(_ _ Hq)->.
(* path goes through the marked component, so z is connected to c *)
left; rewrite -has_predC (eq_has (a2:=fun z=> z \in dom m2)) in Hpxs; last first.
- by move=>q /=; rewrite negbK.
(* q is the last vertex in marked component, xs2 is the free path *)
case: {-1}_ _ _ / (split_findlast Hpxs) (erefl (x::xs))=>{Hpxs} q xs1 xs2 Hq.
rewrite -all_predC (eq_all (a2:=fun z=> z \notin dom m2)) // => Hxs2 Heq.
apply: (connect_trans (y:=q)); rewrite app_predE; first by rewrite -Hm.
case: xs1 Heq=>/=.
- case=>Eq Exs2; rewrite -{q}Eq in Hq *; rewrite -{xs2}Exs2 in Hxs2.
  by apply/connectP; exists xs.
move=>_ t [_ Exs].
apply/connectP; exists xs2; split=>//.
- by move: Hp; rewrite Exs cat_path last_rcons; case/andP.
- by move: Ez; rewrite Exs last_cat last_rcons.
- suff: (edge g (last x t) q) by case/edge_dom=>_ ->; apply: implybT.
  rewrite Exs cat_path rcons_path in Hp.
  by case/andP: Hp; case/andP.
rewrite Exs -cats1 -catA cat1s -cat_cons all_cat in Ha.
by case/andP: Ha.
Qed.

Corollary connectMUnHas p m1 m2 g c (cs : seq ptr) :
  valid (m2 \+ m1) ->
  find p g = Some cs ->
  c \in cs -> good_ptr g c ->
  dom m2 =i connect m1 g c ->
  forall z,
  has (fun x => z \in connect m1 g x) cs =
  (z \in connect m1 g c) ||
  has (fun x => z \in connect (m2 \+ m1) g x) (filter (predC1 c) cs).
Proof.
move=>V Hf Hc Hcd Hm z; apply/iffE; split.
- case/hasP=>x Hx Hz.
  case: (connectMUn V Hf Hc Hcd Hm Hx Hz); first by move=>->.
  by case=>y Hy1 Hy2; apply/orP; right; apply/hasP; exists y.
case/orP; first by move=>Hz; apply/hasP; exists c.
case/hasP=>q; rewrite mem_filter /=; case/andP=>_ Hq /(connectMUnSub V) Hz.
by apply/hasP; exists q.
Qed.

End Marking.

Section NGraph.

Definition n_graph (n : nat) (g : pregraph) : bool :=
  all (fun ns => size ns == n) (range g).

Lemma n_graphUnL n g0 g :
  valid (g \+ g0) ->
  n_graph n (g \+ g0) -> n_graph n g.
Proof.
by move=>V; apply/subset_all=>z; rewrite rangeUn inE V=>->.
Qed.

(* corollary? *)
Lemma n_graphF n g p : n_graph n g -> n_graph n (free g p).
Proof. by apply/subset_all/rangeF. Qed.

Definition get_nth (ps : seq ptr) (n : nat) : ptr :=
  nth null ps n.

Lemma all_good_get p g ps m :
  good_graph g ->
  find p g = Some ps ->
  good_ptr g (get_nth ps m).
Proof.
case/andP=>_ Hg Hf.
case: (ltnP m (size ps))=>Hm; last first.
- by apply/orP; left; rewrite /get_nth; rewrite nth_default.
have /allP : all (good_ptr g) ps.
- move/allP: Hg; apply.
  apply/mem_rangeX; exists p.
  by move/In_find: Hf.
by apply; apply: mem_nth.
Qed.

Lemma all_nth n g :
  n_graph n g ->
  all (fun ns => ns == map (get_nth ns) (iota 0 n)) (range g).
Proof.
move=>H; apply/sub_all/H=>ns /eqP Hns.
apply/eqP/(eq_from_nth (x0:=null)).
- by rewrite size_map size_iota.
by rewrite Hns=>i Hi; rewrite map_nth_iota0 -Hns // take_size.
Qed.

End NGraph.


Section Acyclic.

Definition symconnect p g x y := connect p g x y && connect p g y x.

Lemma symconnect0 p g x : x \in dom g -> x \notin dom p -> symconnect p g x x.
Proof. by move=>Hx Hp; apply/andP; split; apply/connect0. Qed.

Lemma symconnectUn p g0 g x y :
  valid (g \+ g0) ->
  symconnect p g x y -> symconnect p (g \+ g0) x y.
Proof. by move=>V; case/andP=>Hxy Hyx; apply/andP; split; apply: connectUn. Qed.

(* TODO should probably generalize all of this to arbitrary boundary, not Unit *)
Lemma connect_cycle g p : cycle (edge g) p -> {in p &, forall x y, connect Unit g x y}.
Proof.
move=>Hp x y /rot_to[i q Hr]; rewrite -(mem_rot i) Hr => Hy.
have /= Hp1: cycle (edge g) (x :: q) by rewrite -Hr rot_cycle.
have Hd: x \in dom g by move: Hp1; rewrite rcons_path; case/andP=>_ /edge_dom; case.
move: Hp1; case/splitPl: Hy =>r s Hl; rewrite rcons_cat cat_path => /andP[Hxr Hlx].
apply/connectP; exists r; split=>//; first by rewrite Hd implybT.
by rewrite dom0 all_predT.
Qed.

Lemma symconnect_cycle g p : cycle (edge g) p ->
   {in p &, forall x y, symconnect Unit g x y}.
Proof. by move=>Hp x y Hx Hy; rewrite /symconnect !(connect_cycle Hp). Qed.

Lemma symconnect_cycle2P g x y : x != y ->
  reflect (exists2 p, y \in p & cycle (edge g) (x :: p)) (symconnect Unit g x y).
Proof.
move=> Nxy; apply: (iffP idP) => [|[p yp]]; last first.
  by move=> /symconnect_cycle->//; rewrite inE ?eqxx ?yp ?orbT.
move: Nxy =>/[swap]/andP [/connectP[p][Hp {y}-> Np _] /connectP[]].
elim/last_ind => /= [[] _ <-|q z _]; first by rewrite eqxx.
case; rewrite rcons_path last_rcons => /[swap]{z}<- /andP[gq gzq] _ _ Nxy.
have := mem_last x p; rewrite in_cons eq_sym (negPf Nxy)/= => yp.
exists (p ++ q); first by rewrite mem_cat yp.
by rewrite rcons_path cat_path Hp gq last_cat gzq.
Qed.

Definition preacyclic g := all2rel (fun x y => symconnect Unit g x y ==> (x == y)) (dom g).

Lemma preacyclicUn g0 g :
  valid (g \+ g0) ->
  preacyclic (g \+ g0) -> preacyclic g.
Proof.
move=>V /allrelP H; apply/allrelP=>x y Hx Hy; apply/implyP=>Hs.
have Hx1: x \in dom (g \+ g0) by rewrite domUn inE V Hx.
have Hy1: y \in dom (g \+ g0) by rewrite domUn inE V Hy.
move/implyP: (H _ _ Hx1 Hy1); apply.
by apply: symconnectUn.
Qed.

Definition acyclic g := all (fun x => ~~ edge g x x) (dom g) && preacyclic g.

Lemma acyclicUn g0 g :
  valid (g \+ g0) ->
  acyclic (g \+ g0) -> acyclic g.
Proof.
move=>V; case/andP=>Ha Hp; apply/andP; split; last by apply: (preacyclicUn V Hp).
apply/allP=>x Hx.
suff: ~~ edge (g \+ g0) x x by apply/contra/edgeUn.
by move/allP: Ha; apply; rewrite domUn inE V Hx.
Qed.

(* TODO all is overkill here, we only need the head of the path in dom g (?) *)
Lemma acyclic_cycleP g :
  reflect (forall p, ~~ nilp p -> sorted (edge g) p -> all (fun x => x \in dom g) p -> ~~ cycle (edge g) p)
          (acyclic g).
Proof.
rewrite /acyclic; apply: (iffP andP)=>[|Hn]; last first.
- split; first by apply/allP=>x Hx; move: (Hn [::x])=>/=; rewrite !andbT; apply.
  apply/allrelP=>x y Hx _; apply/implyP/contraLR => neqxy.
  apply/symconnect_cycle2P => // -[p Hp] /[dup].
  rewrite [X in X -> _]/= rcons_path => /andP[/[dup] /path_dom Hd Hg Ha].
  by apply/negP/Hn=>//=; rewrite Hx.
case=>/allP Ne /allrelP Ng.
case=>//= x p _; rewrite rcons_path =>/[dup] E ->/=; case/andP=>Hx.
case: p E=>/=; first by move=>_ _; apply: Ne.
move=>y p; case/andP=>He Hp; case/andP=>Hy Ha.
have: ~~ symconnect Unit g x y.
- apply/negP=>Hs; move: (Ng _ _ Hx Hy); rewrite Hs /= =>/eqP Exy.
  by rewrite Exy in He; move: (Ne _ Hy); rewrite He.
apply: contra=>He1; apply: (symconnect_cycle (p:=x::y::p))=>/=; try by rewrite ?(in_cons, eqxx, orbT).
by rewrite rcons_path  He Hp.
Qed.

Lemma acyclic_find g n ns :
  acyclic g ->
  find n g = Some ns ->
  n \notin ns.
Proof.
case/andP=>Ha _ /[dup]Hf /find_some Hn.
move/allP: Ha=>/(_ _ Hn).
by rewrite (find_edge _ Hf) negb_and Hn.
Qed.

End Acyclic.
