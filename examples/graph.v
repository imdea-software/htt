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
From Stdlib Require Import ssreflect ssrfun.
From mathcomp Require Import ssrbool eqtype ssrnat seq path bigop.
From pcm Require Import options axioms pred prelude seqext.
From pcm Require Import heap pcm unionmap natmap auto autouniq autopcm automap.

Abbreviation node := nat.

(**********)
(**********)
(* Graphs *)
(**********)
(**********)

(* link is type with map to seq node that has partial inverse. *)
(* The map/inverse are called links/mk. *)
(* Serves to describe the linkage architecture of a graph. *)
(* V = seq node for general graphs, where each node *)
(* can have arbitrary many children *)
(* V = node * node for binary graphs, where each node *)
(* has at most two children *)

Definition link_axiom V (links : V -> seq node) mk :=
  pcancel links mk /\ ocancel mk links.

HB.mixin Record isLink V := {
  links : V -> seq node;
  mk : seq node -> option V;
  link_subproof : link_axiom links mk}.

#[short(type=link)]
HB.structure Definition Link := {V of isLink V}.

(* repack *)
Lemma links_pcancel {V} : pcancel (@links V) (@mk V).
Proof. by case: (@link_subproof V). Qed.
Lemma links_ocancel {V} : ocancel (@mk V) (@links V).
Proof. by case: (@link_subproof V). Qed.
Lemma inj_links {V} : injective (@links V).
Proof. by apply/pcan_inj/links_pcancel. Qed.

(* link with decidable equality *)
#[short(type="eqlink")]
HB.structure Definition EQLink := {U of Equality U & Link U}.

(* V is the type organizing the edges *)
(* A is the contents/labeling of the nodes *)
(* e.g., pair for binary graphs, sequence for n-ary graphs *)
Record partial_graph' (V : link) (A : Type) :=
  PartialGraph {partialgraph_base : @UM.base node nat_pred (A * V)}.

Section PartialGraphUMC.
Variables (V : link) (A : Type).
Implicit Type f : partial_graph' V A.
Local Coercion partialgraph_base : partial_graph' >-> UM.base.
Let pg_valid f := @UM.valid nat nat_pred (A * V) f.
Let pg_empty := PartialGraph (@UM.empty nat nat_pred (A * V)).
Let pg_undef := PartialGraph (@UM.Undef nat nat_pred (A * V)).
Let pg_upd k v f := PartialGraph (@UM.upd nat nat_pred (A * V) k v f).
Let pg_dom f := @UM.dom nat nat_pred (A * V) f.
Let pg_assocs f := @UM.assocs nat nat_pred (A * V) f.
Let pg_free f k := PartialGraph (@UM.free nat nat_pred (A * V) f k).
Let pg_find k f := @UM.find nat nat_pred (A * V) k f.
Let pg_union f1 f2 := PartialGraph (@UM.union nat nat_pred (A * V) f1 f2).
Let pg_empb f := @UM.empb nat nat_pred (A * V) f.
Let pg_undefb f := @UM.undefb nat nat_pred (A * V) f.
Let pg_from (f : partial_graph' V A) : UM.base _ _ := f.
Let pg_to (b : @UM.base nat nat_pred (A * V)) : partial_graph' V A :=
  PartialGraph b.
Let pg_pts k v := PartialGraph (@UM.pts nat nat_pred (A * V) k v).

Lemma partialgraph_is_umc :
        union_map_axiom pg_valid pg_empty pg_undef pg_upd pg_dom
                        pg_assocs pg_free pg_find pg_union pg_empb
                        pg_undefb pg_pts pg_from pg_to.
Proof. by split=>//; split=>[|[]]. Qed.

HB.instance Definition _ :=
  isUnion_map.Build node nat_pred (A * V)%type
                    (partial_graph' V A) partialgraph_is_umc.
End PartialGraphUMC.

HB.instance Definition _ (V : link) A :=
  isNatMap.Build (A * V)%type (partial_graph' V A).
HB.instance Definition _ (V : eqlink) (A : eqType) :=
  hasDecEq.Build (partial_graph' V A)
                 (@union_map_eqP node _ (A * V)%type (partial_graph' V A)).
Canonical partialgraph_PredType (V : link) A : PredType (node * (A * V)) :=
  um_PredType (partial_graph' V A).
Coercion Pred_of_partialgraph V A
  (x : partial_graph' V A) : {Pred _} := [eta Mem_UmMap x].

(* using nodes g for dom g when g is partial graph *)
Abbreviation nodes g := (domT (partial_graph' _ _) g).
Abbreviation nodes0 g := (null :: nodes g).

(* notation to infer link structure automatically *)
Definition pgx {V : link} A & phant V := partial_graph' V A.
Abbreviation partial_graph V A := (pgx A (Phant V)).

(* general graph linkage and notation *)
Lemma gengraph_is_link : link_axiom id Some. Proof. by []. Qed.
HB.instance Definition _ := isLink.Build (seq node) gengraph_is_link.
Abbreviation pre_graph A := (partial_graph (seq node) A).
Notation "x &-> v" := (ptsT (pre_graph _) x v) (at level 30).

(* binary graph linkage and notation *)
Definition bingraph_link (x : node * node) := [:: x.1; x.2].
Definition bingraph_mk (s : seq node) :=
  if s is [:: a; b] then Some (a, b) else None.
Arguments bingraph_link x /.
Arguments bingraph_mk s /.
Lemma bingraph_is_link : link_axiom bingraph_link bingraph_mk.
Proof. by split; case=>// a [] // b []. Qed.
HB.instance Definition _ := 
  isLink.Build (prod node node) bingraph_is_link.
Abbreviation binary_graph A := (partial_graph (node * node) A).
Notation "x &2-> v" := (ptsT (binary_graph _) x v) (at level 30).

(********************************)
(* labels, adj, children, edges *)
(********************************)

(* basic operations over graphs *)

Section GraphDefs.
Context {V : link} {A : Type}.
Implicit Type g : partial_graph V A.

(* maps each node to its contents (ie. label) *)
Definition labels g : nmap A := mapv fst g.
HB.instance Definition _ := OmapFun.copy labels labels.
Definition olabel g x := find x (labels g).

(* adjacency list of x includes all nodes with edges from x *)
(* explicitly including dangling edges *)
Definition adj g x := oapp (links \o snd) [::] (find x g).

(* children is like adj, but removes dangling edges *)
Definition children g x : seq node := filter [in nodes g] (adj g x).

(* edge is applicative variant of children *)
(* thus, dangling edges are *not* edges. *)
Definition edge g : rel node := mem \o children g.
End GraphDefs.

Arguments edge {V A} g x y : simpl never.

Section GraphLemmas.
Context {V : link} {A : Type}.
Implicit Type g : partial_graph V A.

(* nodes lemmas *)

Lemma nodes_undef : nodes (undef : partial_graph V A) = [::].
Proof. by []. Qed.

Lemma nodes0_undef : nodes0 (undef : partial_graph V A) = [:: null].
Proof. by []. Qed.

Lemma nodes_unit : nodes (Unit : partial_graph V A) = [::].
Proof. by []. Qed.

Lemma nodes0_unit : nodes0 (Unit : partial_graph V A) = [:: null].
Proof. by []. Qed.

Lemma nodesPtUn x y v g :
        valid (pts x v \+ g) ->
        (y \in nodes (pts x v \+ g)) = (x == y) || (y \in nodes g).
Proof. by move=>W; rewrite domPtUn inE W. Qed.

Lemma nodes0PtUn x y v g :
        valid (pts x v \+ g) ->
        (y \in nodes0 (pts x v \+ g)) = (x == y) || (y \in nodes0 g).
Proof. by move=>W; rewrite inE nodesPtUn // orbCA. Qed.

Lemma nodesUn g1 g2 :
        valid (g1 \+ g2) ->
        nodes (g1 \+ g2) =i nodes g1 ++ nodes g2.
Proof. by move=>W x; rewrite domUn inE W mem_cat. Qed.

Lemma nodesUn0L g1 g2 x :
        valid (g1 \+ g2) ->
        (x \in nodes0 (g1 \+ g2)) = (x \in nodes0 g1) || (x \in nodes g2).
Proof. by move=>W; rewrite !inE -orbA -domUnE. Qed.

Lemma nodesUn0R g1 g2 x :
        valid (g1 \+ g2) ->
        (x \in nodes0 (g1 \+ g2)) = (x \in nodes g1) || (x \in nodes0 g2).
Proof. by move=>W; rewrite !inE orbCA -domUnE. Qed.

(* labels lemmas *)

Lemma In_labelsX g x v :
        (x, v) \In labels g <->
        exists xs, (x, (v, xs)) \In g.
Proof.
rewrite In_omfX; split; last by case=>lks H; exists (v, lks).
by case; case=>w lks /= H [<-{v}]; exists lks.
Qed.

Lemma In_labels g x xs :
        (x, xs) \In g ->
        (x, xs.1) \In labels g.
Proof. by case: xs=>v lks; rewrite In_labelsX; exists lks. Qed.

Lemma In_olabel g x xs :
        (x, xs) \In g ->
        olabel g x = Some xs.1.
Proof. by rewrite /olabel=>/In_labels/In_find ->. Qed.

(* adjacency list lemmas *)

Lemma adj_undef x : adj (undef : partial_graph V A) x = [::].
Proof. by []. Qed.

Lemma adj_unit x : adj (Unit : partial_graph V A) x = [::].
Proof. by []. Qed.

Lemma adjND g x :
        x \notin nodes g ->
        adj g x = [::].
Proof. by rewrite /adj/oapp; case: dom_find. Qed.

Lemma adjUnL g1 g2 x :
        valid (g1 \+ g2) ->
        adj (g1 \+ g2) x =
        if x \in nodes g1 then adj g1 x else adj g2 x.
Proof. by move=>W; rewrite /adj/oapp findUnL //; case: dom_find. Qed.

Lemma adjUnR g1 g2 x :
        valid (g1 \+ g2) ->
        adj (g1 \+ g2) x =
        if x \in nodes g2 then adj g2 x else adj g1 x.
Proof. by rewrite joinC=>/adjUnL; apply. Qed.

Lemma size_adj g x :
        size (adj g x) > 0 ->
        x \in nodes g.
Proof. by rewrite /adj/oapp; case: dom_find. Qed.

Lemma adjD g x y :
        y \in adj g x ->
        x \in nodes g.
Proof. by move=>X; apply: size_adj; case: (adj g x) X. Qed.

Lemma adjV g x y :
        y \in adj g x ->
        valid g.
Proof. by move/adjD/dom_valid. Qed.

Lemma In_graph g x v xs :
        (x, (v, xs)) \In g ->
        adj g x = links xs.
Proof. by rewrite /adj/oapp=>/In_find ->. Qed.

Lemma In_graphX g x :
        x \in nodes g ->
        exists v xs, (x, (v, xs)) \In g /\ adj g x = links xs.
Proof. by case/In_domX=>-[v xs] /[dup]/In_graph; eauto. Qed.

Lemma graph_eta g x v :
        (x, v) \In g ->
        g = pts x v \+ free g x.
Proof. exact: In_eta. Qed.

Lemma range_adj g x :
        x \in nodes g ->
        adj g x \in map (links \o snd) (range g).
Proof.
by case/In_graphX=>v [xs][] /In_range/(Mem_map (links \o snd))/mem_seqP H ->.
Qed.

Lemma adjF g x y :
        adj (free g x) y = if x == y then [::] else adj g y.
Proof. by rewrite /adj findF eq_sym; case: eqP. Qed.

Lemma adjPt2 v x xs y :
        adj (pts x (v, xs) : partial_graph V A) y =
        if (x != 0) && (y == x) then links xs else [::].
Proof. by rewrite /adj findPt2 andbC; case: ifP. Qed.

Lemma adjPt v x xs :
        adj (pts x (v, xs) : partial_graph V A) x =
        if x != 0 then links xs else [::].
Proof. by rewrite adjPt2 eqxx andbT. Qed.

(* children lemmas *)

Lemma children_undef x : children (undef : partial_graph V A) x = [::].
Proof. by []. Qed.

Lemma children_unit x : children (Unit : partial_graph V A) x = [::].
Proof. by []. Qed.

Lemma childrenND g x :
        x \notin nodes g ->
        children g x = [::].
Proof. by rewrite /children=>/adjND ->. Qed.

Lemma childrenD g x :
        {subset children g x <= nodes g}.
Proof. by move=>y; rewrite /children mem_filter; case/andP. Qed.

Lemma childrenUnL g1 g2 x :
        valid (g1 \+ g2) ->
        {subset children g1 x <= children (g1 \+ g2) x}.
Proof.
move=>W y; rewrite /children !mem_filter /= =>/andP [Dy Ly].
by rewrite domUn inE W Dy adjUnL //= (adjD Ly).
Qed.

Lemma childrenUnR g1 g2 x :
        valid (g1 \+ g2) ->
        {subset children g2 x <= children (g1 \+ g2) x}.
Proof. by rewrite joinC; apply: childrenUnL. Qed.

Lemma children_adj g x :
        {subset children g x <= adj g x}.
Proof. by move=>z; rewrite /children mem_filter=>/andP []. Qed.

(* if x is node in g then g x contains all children of x *)
(* and maybe some more nodes that aren't in g *)
Lemma range_children g x :
        x \in nodes g ->
        exists2 xs, xs \in map (links \o snd) (range g) &
                    {subset children g x <= xs}.
Proof.
move=>Dx; exists (adj g x); first by apply: range_adj.
by apply: children_adj.
Qed.

(* edge lemmas *)

Lemma edge_undef x y : edge (undef : partial_graph V A) x y = false.
Proof. by rewrite /edge/= children_undef. Qed.

Lemma edge_unit x y : edge (Unit : partial_graph V A) x y = false.
Proof. by rewrite /edge/= children_unit. Qed.

Lemma edge_children g x y :
        edge g x y = (y \in children g x).
Proof. by []. Qed.

Lemma edgeUnL g1 g2 x y :
        valid (g1 \+ g2) ->
        edge g1 x y ->
        edge (g1 \+ g2) x y.
Proof. by move=>W; apply: childrenUnL. Qed.

Lemma edgeUnR g1 g2 x y :
        valid (g1 \+ g2) ->
        edge g2 x y ->
        edge (g1 \+ g2) x y.
Proof. by move=>W; apply: childrenUnR. Qed.

Lemma edgeD g x y :
        edge g x y ->
        (x \in nodes g) * (y \in nodes g).
Proof.
rewrite /edge/= => H; split; last by apply: childrenD H.
by apply: contraLR H=>/childrenND ->.
Qed.

Lemma edge_adj g x y :
        edge g x y = (y \in nodes g) && (y \in adj g x).
Proof. by rewrite /edge/= mem_filter /=; case: dom_find. Qed.

Lemma edgeA g x y :
        edge g x y ->
        y \in adj g x.
Proof. by rewrite edge_adj=>/andP []. Qed.

Lemma edgeV g x y :
        edge g x y ->
        valid g.
Proof. by move/edgeA/adjV. Qed.

Lemma adj_edge g x y :
        y \in nodes g ->
        y \in adj g x ->
        edge g x y.
Proof. by rewrite edge_adj=>->->. Qed.

Lemma subrel_edgeL g1 g2 :
        valid (g1 \+ g2) ->
        subrel (edge g1) (edge (g1 \+ g2)).
Proof.
by move=>W a b /[dup]/edgeD [Da Db]; rewrite !edge_adj ?(adjUnL,domUnE,Da,Db).
Qed.

Lemma subrel_edgeR g1 g2 :
        valid (g1 \+ g2) ->
        subrel (edge g2) (edge (g1 \+ g2)).
Proof. by rewrite joinC; apply: subrel_edgeL. Qed.

Lemma path_nodes g x xs :
        path (edge g) x xs ->
        {subset xs <= nodes g}.
Proof.
elim: xs x=>[|b xs IH]x //= /andP [/edgeD [_ He] /IH].
by apply: subset_consLI He.
Qed.

Lemma path_nodes0 g x xs :
        path (edge g) x xs ->
        nilp xs || (x \in nodes g).
Proof. by case: xs=>[|y xs] //= /andP [] /edgeD []. Qed.

Lemma edgeFE g x a b :
        (edge (free g x) a b) =
        [&& edge g a b, x != a & x != b].
Proof.
rewrite /edge/children/adj/= !mem_filter /= domF findF -!(eq_sym x).
case: (x =P a)=>[<-{a}|_]; first by rewrite !andbF.
case D: (find a g)=>[c|/=]; last by rewrite !andbF.
case C: (b \in links c.2); last by rewrite !andbF.
by rewrite !andbT andbC.
Qed.

Lemma edge_free_eq g (x : node) (xs : seq node) :
        x \notin xs ->
        {in xs &, edge g =2 edge (free g x)}.
Proof.
move=>N a b Ax Bx; rewrite edgeFE; case Eg2: (edge g a b)=>//=.
by case: eqP Ax N=>[<- ->//|_] Ax; case: eqP Bx=>//= <- ->.
Qed.

Lemma edge_free_sub g (x : node) (xs : seq node) :
        x \notin xs ->
        {in xs &, subrel (edge g) (edge (free g x))}.
Proof. by move=>N a b Ax /(edge_free_eq g N Ax) <-. Qed.

Lemma free_edge_sub {g} {x : node} :
        subrel (edge (free g x)) (edge g).
Proof. by move=>y z; rewrite edgeFE=>/and3P []. Qed.

Lemma path_edge_free g x y ys:
        x \notin y :: ys ->
        path (edge g) y ys ->
        path (edge (free g x)) y ys.
Proof. by move=>N; rewrite -(eq_in_path (edge_free_eq g N)). Qed.

(* useful renaming *)
Lemma edge_free_path g x y ys:
        path (edge (free g x)) y ys ->
        path (edge g) y ys.
Proof. exact: (sub_path free_edge_sub). Qed.

End GraphLemmas.

Prenex Implicits In_graph.

(***********************)
(* Depth-first search  *)
(***********************)

(* lifts dfs from mathcomp fingraph to partial graphs *)

(* list of nodes traversed by depth-first search of g *)
(* at depth n, starting from x, and avoiding v. *)
(* Definition uses children, not links; *)
(* thus, it doesn't follow dangling edges *)
(* and dfs can't express reachability to an outside node. *)
(* If the latter is desired, it can be separately defined *)
(* as a conjunct of dfs and links properties. *)

Fixpoint dfs (V : link) A (g : partial_graph V A) (n : nat) (v : seq node) x :=
  if (x \notin dom g) || (x \in v) then v else
  if n is n'.+1 then foldl (dfs g n') (x :: v) (children g x) else v.

Section DFSLemmas.
Context {V : link} {A : Type}.
Implicit Type g : partial_graph V A.

Lemma dfs_notin g n v x :
        x \notin nodes g ->
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
Lemma subset_foldl_dfs_nodes g n v x :
        {subset v <= nodes g} ->
        {subset foldl (dfs g n) v x <= nodes g}.
Proof.
elim: n x v=>[|n IHn]; elim=>[|x xs IHx] v //=.
- by case: ifP=>_; apply: IHx.
case: ifP; first by case: (x \in nodes g)=>//= H; apply: IHx.
case Dx: (x \in nodes g)=>//= H Gx; apply/IHx/IHn.
by move=>z; rewrite inE; case/orP=>[/eqP ->|/Gx].
Qed.

Lemma subset_dfs_nodes g n v x :
        {subset v <= nodes g} ->
        {subset dfs g n v x <= nodes g}.
Proof.
case: n=>[|n] H /=; case: ifP=>//=.
case Dx : (x \in nodes g)=>//= _; apply: subset_foldl_dfs_nodes.
by move=>z; rewrite inE; case/orP=>[/eqP ->|/H].
Qed.

Lemma uniq_dfs_foldl g n v x :
        uniq v ->
        uniq (foldl (dfs g n) v x).
Proof.
elim: n x v=>[|n IHn]; elim=>[|x xs IHx] v U //=; apply: IHx.
- by rewrite if_same.
case: (x \in nodes g)=>//=; case: ifP=>// Xv.
by rewrite IHn //= Xv.
Qed.

Lemma uniq_dfs g n v x :
        uniq v ->
        uniq (dfs g n v x).
Proof.
case: n=>[|n] U /=; first by rewrite if_same.
case: (x \in nodes g)=>//=; case: ifP=>// Xv.
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
        size (nodes g) <= size v + n ->
        uniq v ->
        {subset v <= nodes g} ->
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
set v1 := x :: v; set c := children g x; have [->|/eqP Nyx] := eqVneq y x.
- by rewrite subset_dfs ?inE ?eqxx //; apply/ReflectT/dfs_path_id.
apply: (@equivP (exists2 x1, x1 \in c & dfs_path g v1 x1 y))=>/=; last first.
- split=>{IHn} [[x1 Hx1 [p1 P1 E1 D1]]|[p /shortenP []]].
  - apply: (DfsPath (xs:=x1::p1))=>//=; first by rewrite edge_children -/c Hx1.
    by rewrite disjoint_consR Vx (disjoint_consLE D1).
  case=>[_ _ _ /Nyx|] //= x1 xs /andP [Hx1 Hp1] /and3P [N1 _ _] S1 E1 D1.
  exists x1=>//; apply: (DfsPath (xs:=xs))=>//; rewrite disjoint_consL N1.
  by rewrite (disjoint_consRE (disjoint_subL (subset_consLR S1) D1)).
move: (Dx).
have {Nyx Ny} : y \notin v1 by apply/norP; move/eqP: Nyx.
have {Sv Dx} : {subset v1 <= nodes g} by apply: subset_consLI.
have {Vx Uv} : uniq v1 by rewrite /= Vx.
have {Hv} : size (nodes g) <= size v1 + n by rewrite addSnnS.
have : {subset c <= nodes g} by apply: childrenD.
elim: {x v}c (x) v1=>[|x xs IHa] x' v /= Dxs Hv U Sv Nv Dx'.
- by rewrite (negbTE Nv); apply: ReflectF; case.
have Dx : x \in nodes g by apply: Dxs; rewrite inE eqxx.
have Da : {subset xs <= nodes g} by move=>z Z; apply/Dxs/subset_consR.
set v2 := dfs g n v x.
have Sv2 : {subset v <= v2} := @subset_dfs g n v [:: x].
have [Hy2|Ny2] := boolP (y \in v2).
- rewrite subset_dfs //; apply: ReflectT.
  by exists x; [rewrite inE eq_refl|apply/IHn].
apply: {IHa} (equivP (IHa _ _ _ _ _ _ Ny2 Dx))=>//.
- by rewrite (leq_trans Hv) ?leq_add2r ?uniq_leq_size.
- by rewrite uniq_dfs.
- by apply: subset_dfs_nodes.
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

End DFSLemmas.

(*******************)
(* Filter by nodes *)
(*******************)

(* select subgraph consisting of nodes *)
(* that satisfy a predicate *)

Definition kfiltx {V : link} A (xs : pred node) (g : partial_graph V A) :
  partial_graph V A := um_filterk xs g.
HB.instance Definition _ V A xs :=
  OmapFun.copy (@kfiltx V A xs) (@kfiltx V A xs).
Abbreviation kfilt g xs := (@kfiltx _ _ xs g).

Section Kfilt.
Context {V : link} {A : Type}.
Implicit Type g : partial_graph V A.

Lemma kfiltUn g (p1 p2 : pred node) :
         (forall x, x \in p1 -> ~ x \in p2) ->
         kfilt g (predU p1 p2) = kfilt g p1 \+ kfilt g p2.
Proof. by move=>H; apply: umfilt_dpredU=>x /H/negP. Qed.

Lemma kfilt_predI g (p1 p2 : pred node) :
         kfilt g (predI p1 p2) = kfilt (kfilt g p2) p1.
Proof. by rewrite /kfiltx umfilt_predI. Qed.

Lemma kfilt_predIC g (p1 p2 : pred node) :
         kfilt g (predI p1 p2) = kfilt (kfilt g p1) p2.
Proof. by rewrite /kfiltx umfiltC umfilt_predI. Qed.

Lemma kfilt_predD g (p1 p2 : pred node) :
        {subset p1 <= p2} ->
        kfilt g p2 = kfilt g p1 \+ kfilt g (predD p2 p1).
Proof. by move=>S; apply: umfilt_predD; case=>? /= _; apply: S. Qed.

Lemma eq_in_kfilt g (p1 p2 : pred node) :
        {in nodes g, p1 =1 p2} ->
        kfilt g p1 = kfilt g p2.
Proof. exact: eq_in_umfiltk. Qed.

Lemma kfilt_eq g (p1 p2 : pred node) :
        p1 =1 p2 ->
        kfilt g p1 = kfilt g p2.
Proof. by move=>N; apply: eq_in_kfilt. Qed.

Lemma adj_kfilt g p x :
        adj (kfilt g p) x =
        if p x then adj g x else [::].
Proof. by rewrite /adj find_umfiltk; case: (p x). Qed.

Lemma children_kfilt g p x y :
        (y \in children (kfilt g p) x) =
        [&& p x, p y & y \in children g x].
Proof.
rewrite /children !mem_filter /= adj_kfilt dom_umfiltk inE -andbA.
by case: (p x)=>//=; rewrite !andbF.
Qed.

Lemma edge_kfilt g (p : pred node) x y :
        edge (kfilt g p) x y = [&& x \in p, y \in p & edge g x y].
Proof. by rewrite /edge /= children_kfilt. Qed.

Lemma edge_kfiltE g (p : pred node) :
        {in p &, edge (kfilt g p) =2 edge g}.
Proof. by move=>x y X Y; rewrite edge_kfilt X Y. Qed.

Lemma nodes_kfiltE g (p : pred node) :
        nodes (kfilt g p) = filter p (nodes g).
Proof. by rewrite dom_umfiltkE. Qed.

Lemma nodes_kfilt g (p : pred node) x :
        (x \in nodes (kfilt g p)) = (x \in nodes g) && (x \in p).
Proof. by rewrite nodes_kfiltE mem_filter andbC. Qed.

Lemma kfilt_nodesE g (p : pred node) :
        {subset nodes g <= p} <->
        kfilt g p = g.
Proof. exact: umfiltk_subdomE. Qed.

Lemma kfilt_nodes g (p : pred node) :
        {subset nodes g <= p} ->
        kfilt g p = g.
Proof. by move/kfilt_nodesE. Qed.

Lemma find_kfilt g (p : pred node) x :
        find x (kfilt g p) =
        if x \in p then find x g else None.
Proof. exact: find_umfiltk. Qed.

Lemma edge_kfilt_sub g p :
        subrel (edge (kfilt g p)) (edge g).
Proof. by move=>a b; rewrite edge_kfilt; case/and3P. Qed.

Lemma edge_kfilt_in_sub g p :
        {in p &, subrel (edge g) (edge (kfilt g p))}.
Proof. by move=>a b Ax Bx; rewrite edge_kfilt Ax Bx. Qed.

Lemma edge_kfilt_mono g (p1 p2 : pred node) :
        {subset p1 <= p2} ->
        {in p1 &, subrel (edge (kfilt g p1)) (edge (kfilt g p2))}.
Proof. by move=>H a b Ax Bx; rewrite !edge_kfiltE //; apply: H. Qed.

Lemma kfilt_nodesI g (p : pred node) :
        kfilt g p = kfilt g [predI nodes g & p].
Proof. by rewrite kfilt_predIC [in RHS](@kfilt_nodes g). Qed.

Lemma kfiltC g (p : pred node) :
        g = kfilt g p \+ kfilt g (predC p).
Proof. exact: umfilt_predC. Qed.

Lemma kfiltC1 g x : kfilt g (predC1 x) = free g x.
Proof. exact: umfiltkC1. Qed.

Lemma kfiltUn_nodes g1 g2 :
        [pcm g1 <= g2] ->
        valid g2 ->
        kfilt g2 [in nodes g1] = g1.
Proof. by case=>g -> W; rewrite /kfiltx umfiltk_dom. Qed.

Lemma In_nodes_kfiltX g (p : pred node) x :
        reflect (exists v xs, (x, (v, xs)) \In g /\ p x)
                (x \in nodes (kfilt g p)).
Proof.
by case: In_dom_umfilt=>H; constructor; [case: H=>-[]|case=>v [?][]]; eauto.
Qed.

End Kfilt.

Arguments edge_kfilt_in_sub {V A g p}.

(**********************)
(* Filter by contents *)
(**********************)

(* select subgraph consisting of nodes *)
(* whose contents is in the given list of contents *)

Definition cfiltx {V : link} {A : eqType} (xs : seq A) g :
  partial_graph V A := um_filterv (mem xs \o fst) g.
HB.instance Definition _ V A xs :=
  OmapFun.copy (@cfiltx V A xs) (@cfiltx V A xs).
Abbreviation cfilt g xs := (@cfiltx _ _ xs g).

Section Cfilt.
Context {V : link} {A : eqType}.
Implicit Types (g : partial_graph V A) (xs : seq A).

(* equalities by side-conditions *)

Lemma eq_in_cfilt g xs1 xs2 :
        {in range (labels g), xs1 =i xs2} ->
        cfilt g xs1 = cfilt g xs2.
Proof.
move=>H; apply: eq_in_umfiltv; case=>v k /In_rangeX [x /In_labels X].
by apply/H/mem_range/X.
Qed.

Lemma id_in_cfilt g xs :
        {subset range (labels g) <= xs} ->
        cfilt g xs = g.
Proof.
by move=>H; rewrite omf_some /omfx //= =>-[k [v a]] /In_labels/mem_range/H ->.
Qed.

Lemma in_cfilt0 g xs :
        valid g ->
        {subset range (labels g) <= predC (mem xs)} ->
        cfilt g xs = Unit.
Proof.
by move=>W H; apply: umfilt_mem0L=>//= k [v a] /In_labels/mem_range/H.
Qed.

(* equalities by reducing to sets of nodes *)

Lemma eq_cfiltD g (xs1 xs2 : seq A) :
        nodes (cfilt g xs1) =i nodes (cfilt g xs2) ->
        cfilt g xs1 = cfilt g xs2.
Proof. exact: eq_umfiltD. Qed.

Lemma id_cfiltD g (xs : seq A) :
        nodes (cfilt g xs) =i nodes g ->
        cfilt g xs = g.
Proof. exact: id_umfiltD. Qed.

(* equalities by complementary sequences *)

Lemma cfiltC g xs1 xs2 :
        {in range (labels g), xs2 =i [predC xs1]} ->
        cfilt g xs1 \+ cfilt g xs2 = g.
Proof.
move=>H; rewrite [RHS](umfilt_predC g (mem xs1 \o fst \o snd)).
congr (_ \+ _); apply/eq_in_umfilt=>-[k [v a]] /In_labels/mem_range /=.
by move/H=>->.
Qed.

Lemma cfiltCE g xs1 xs2 :
        {in range (labels g), xs2 =i [predC xs1]} ->
        cfilt g xs2 = Unit ->
        cfilt g xs1 = g.
Proof. by move/cfiltC=>/[swap] E; rewrite E unitR. Qed.

(* prefixing everything with nodes can avoid a check for validity *)
Lemma nodes_cfiltCE g xs1 xs2 :
        {in range (labels g), xs2 =i [predC xs1]} ->
        nodes (cfilt g xs2) =i [::] ->
        nodes (cfilt g xs1) = nodes g.
Proof.
case: (normalP g)=>[->//|W] E.
have Vg : valid (cfilt g xs2) by rewrite pfVE.
by move/(dom0E Vg)/cfiltCE->.
Qed.

(* cfilt with nodes, find, free, union *)

Lemma nodes_cfiltE g xs x :
        (x \in nodes (cfilt g xs)) =
        if find x g is Some v then v.1 \in xs else false.
Proof.
rewrite dom_umfiltE mem_filter.
by case: dom_find=>//= v; rewrite andbT.
Qed.

Lemma nodes_cfiltX a g xs x :
        (x \in nodes (cfilt g xs)) =
        (x \in nodes g) && (odflt a (olabel g x) \in xs).
Proof. by rewrite nodes_cfiltE /olabel find_omf /omfx; case: dom_find. Qed.

Lemma nodes_cfilt g xs x v :
        (x, v) \In g ->
        (x \in nodes (cfilt g xs)) = (v.1 \in xs).
Proof. by rewrite nodes_cfiltE=>/In_find ->. Qed.

Lemma find_cfilt g xs x :
        find x (cfilt g xs) =
        if find x g is Some v then
          if v.1 \in xs then Some v else None
        else None.
Proof. exact: find_umfilt. Qed.

Lemma cfiltF g xs x : cfilt (free g x) xs = free (cfilt g xs) x.
Proof. exact: omfF. Qed.

(* union and cons lemmas stated with relativized side-conditions *)

Lemma cfiltUnX g xs1 xs2 :
        {in range (labels g), {subset xs1 <= [predC xs2]}} ->
        cfilt g (xs1 ++ xs2) = cfilt g xs1 \+ cfilt g xs2.
Proof.
move=>H; rewrite /cfiltx (umfiltv_predD (q1 := mem xs1 \o fst)).
- by move=>x /=; rewrite mem_cat=>->.
congr (_ \+ _); apply: eq_in_umfiltv; case=>k a X /=.
rewrite mem_cat; case D: (k \in xs1)=>//=.
case/In_rangeX: X=>b /In_labels/mem_range=>/= X.
by move/negbTE: (H k X D).
Qed.

Lemma cfilt_consX g x xs :
        {in range (labels g), forall x, x \notin xs} ->
        cfilt g (x :: xs) = cfilt g [:: x] \+ cfilt g xs.
Proof. by move=>H; rewrite -cat1s cfiltUnX // => z /H. Qed.

(* union and cons lemma variants with boolean *)
(* non-relativized side-conditions *)
(* useful for automated discharge *)

Lemma cfiltUn g xs1 xs2 :
        all (predC (mem xs2)) xs1 ->
        cfilt g (xs1 ++ xs2) = cfilt g xs1 \+ cfilt g xs2.
Proof. by move/allP=>H; apply/cfiltUnX=>z _; apply: H. Qed.

Lemma cfilt_cons g x xs :
        x \notin xs ->
        cfilt g (x :: xs) = cfilt g [:: x] \+ cfilt g xs.
Proof. by move=>H; rewrite -cat1s cfiltUn //= H. Qed.

(* intersections *)

Lemma cfilt_predI g xs1 xs2 :
        cfilt (cfilt g xs1) xs2 = cfilt g (filter (mem xs1) xs2).
Proof.
rewrite /cfiltx -umfilt_predI -eq_in_umfilt.
by case=>k v /=; rewrite mem_filter andbC.
Qed.

Lemma cfilt_predIC g xs1 xs2 :
        cfilt (cfilt g xs1) xs2 = cfilt g (filter (mem xs2) xs1).
Proof.
by rewrite cfilt_predI; apply: eq_in_cfilt=>W _; apply: filter_mem_sym.
Qed.

Lemma nodes_cfiltI g xs1 xs2 x :
        (x \in nodes (cfilt (cfilt g xs1) xs2)) =
        (x \in nodes (cfilt g xs1)) && (x \in nodes (cfilt g xs2)).
Proof.
rewrite !nodes_cfiltE find_cfilt; case: dom_find=>// v _ _.
by case: ifP.
Qed.

Lemma cfilt_nil g :
        valid g ->
        cfilt g [::] = Unit.
Proof. exact: umfilt_pred0. Qed.

(* memebership in disjoint filters: prop variant *)

Lemma nodes_cfiltNX g xs1 xs2 x :
        all (predC (mem xs2)) xs1 ->
        x \in nodes (cfilt g xs1) ->
        ~ x \in nodes (cfilt g xs2).
Proof.
move/all_filterPC=>E D1 D2.
have : x \in nodes (cfilt g (filter (mem xs2) xs1)).
- by rewrite -cfilt_predI nodes_cfiltI D1 D2.
rewrite E cfilt_nil //.
by case/In_domX: D1=>v /In_umfiltX [_] /In_valid.
Qed.

Lemma nodes0_cfiltNX g xs1 xs2 x :
        all (predC (mem xs2)) xs1 ->
        x \in nodes0 (cfilt g xs1) ->
        ~ x \in nodes (cfilt g xs2).
Proof.
rewrite !inE=>X /orP [/eqP -> /dom_cond //|].
by apply: nodes_cfiltNX.
Qed.

(* membership in disjoint filters: bool variant *)

Lemma nodes_cfiltN g xs1 xs2 x :
        all (predC (mem xs2)) xs1 ->
        x \in nodes (cfilt g xs1) ->
        x \notin nodes (cfilt g xs2).
Proof. by move=>E X; apply/negP/(nodes_cfiltNX E X). Qed.

Lemma nodes0_cfiltN g xs1 xs2 x :
        all (predC (mem xs2)) xs1 ->
        x \in nodes0 (cfilt g xs1) ->
        x \notin nodes (cfilt g xs2).
Proof.
move=>E; rewrite inE; case/orP=>[/eqP ->|/(nodes_cfiltN E)//].
by rewrite cond_dom.
Qed.

(* membership in subfilters: positive versions *)

Lemma nodes_cfiltS g xs1 xs2 x :
        all (mem xs2) xs1 ->
        x \in nodes (cfilt g xs1) ->
        x \in nodes (cfilt g xs2).
Proof.
move/allP=>X; rewrite !nodes_cfiltE.
by case: (find x g)=>// -[z v] /X.
Qed.

Lemma nodes0_cfiltS g xs1 xs2 x :
        all (mem xs2) xs1 ->
        x \in nodes0 (cfilt g xs1) ->
        x \in nodes0 (cfilt g xs2).
Proof.
move=>X; rewrite !inE=>/orP [->|/(nodes_cfiltS X)->] //.
by rewrite orbT.
Qed.

(* membership in subfilters: negative versions *)

Lemma nodes_cfiltSN g xs1 xs2 x :
        all (mem xs2) xs1 ->
        x \notin nodes (cfilt g xs2) ->
        x \notin nodes (cfilt g xs1).
Proof. by move=>X; apply/contra/nodes_cfiltS. Qed.

Lemma nodes0_cfiltSN g xs1 xs2 x :
        all (mem xs2) xs1 ->
        x \notin nodes0 (cfilt g xs2) ->
        x \notin nodes (cfilt g xs1).
Proof.
by move=>X; rewrite inE negb_or; case/andP=>_ /nodes_cfiltSN; apply.
Qed.

Lemma nodes00_cfiltSN g xs1 xs2 x :
        all (mem xs2) xs1 ->
        x \notin nodes0 (cfilt g xs2) ->
        x \notin nodes0 (cfilt g xs1).
Proof. by move=>X; apply/contra/nodes0_cfiltS. Qed.

Lemma nodes_cfiltC g xs1 xs2 x :
        {in range (labels g), xs2 =i [predC xs1]} ->
        (x \in nodes g) =
          (x \in nodes (cfilt g xs1)) ||
          (x \in nodes (cfilt g xs2)).
Proof.
move=>E; case: (normalP g)=>[->//|W].
rewrite -{1}(cfiltC E) domUn inE -cfiltUnX ?pfVE ?W //.
by move=>z {}/E E; rewrite inE /= E inE negbK.
Qed.

Lemma nodes0_cfiltC g xs1 xs2 x :
        {in range (labels g), xs2 =i [predC xs1]} ->
        x \notin nodes0 (cfilt g xs1) ->
        (x \in nodes0 g) = (x \in nodes (cfilt g xs2)).
Proof.
rewrite !inE negb_or => E /andP [/negbTE ->] /= X.
by rewrite (nodes_cfiltC x E) (negbTE X).
Qed.

Lemma adj_cfiltS g xs x :
        {subset adj (cfilt g xs) x <= adj g x}.
Proof.
by move=>z; rewrite /adj find_cfilt /=; case: (find x g)=>//=a ; case: ifP.
Qed.

End Cfilt.

Arguments nodes0_cfiltC {V A g xs1} xs2 {x _}.
Arguments nodes_cfiltCE {V A g xs1}.

(* interaction of cfilt and kfilt *)

Section CfiltKfilt.
Context {V : link} {A : eqType}.
Implicit Types (g : partial_graph V A) (p : pred node) (xs : seq A).

Lemma ckfilt g p xs :
        cfilt (kfilt g p) xs = kfilt (cfilt g xs) p.
Proof.
rewrite /cfiltx/kfiltx -!umfilt_predI.
by apply/eq_in_umfilt; case=>k v H /=; rewrite andbC.
Qed.

(* different name for the other direction *)
Lemma kcfilt g p xs :
        kfilt (cfilt g xs) p = cfilt (kfilt g p) xs.
Proof. by rewrite ckfilt. Qed.

End CfiltKfilt.

(******************************)
(* Updating single graph node *)
(******************************)

(* according to function f that *)
(* modifies node's contents and linkage *)

Definition updgf {V : link} {A} x (f : A * V -> A * V)
    (g : partial_graph V A) : partial_graph V A :=
  if find x g is Some v then upd x (f v) g else undef.

Section UpdgLemmas.
Context {V : link} {A : Type}.
Implicit Types (g : partial_graph V A) (f : A * V -> A * V).

Lemma nodesUg x f g :
        nodes (updgf x f g) =
        if x \in nodes g then nodes g else [::].
Proof.
rewrite /updgf; case: dom_find=>[//|[k v] /In_find H].
by rewrite domUE // (In_dom H).
Qed.

Lemma adjUg x f g a :
        adj (updgf x f g) a =
        if find x g is Some v then
          if a == x then links (f v).2
          else adj g a
        else [::].
Proof.
rewrite /updgf/adj; case: (dom_find x g)=>[//|[k v] /In_find H _].
by rewrite findU (In_cond H) (In_valid H); case: (a =P x).
Qed.

Lemma childrenUg x f g a :
        children (updgf x f g) a =
        if find x g is Some v then
          if a == x then filter [in nodes g] (links (f v).2)
          else children g a
        else [::].
Proof.
rewrite /children adjUg nodesUg.
case: (dom_find x g)=>[//|[k v] /In_find H _].
by case: (a =P x).
Qed.

Lemma edgeUg x f g a b :
        edge (updgf x f g) a b =
        if find x g is Some v then
          if a == x then (b \in nodes g) && (b \in links (f v).2)
          else edge g a b
        else false.
Proof.
rewrite /updgf/edge/= !mem_filter /adj.
case: (dom_find x g)=>[//|[k v] /In_find H _].
rewrite domUE ?(In_dom H) // findU (In_cond H) (In_valid H) /=.
by case: (a =P x).
Qed.

Lemma findUg x y f g :
        find x (updgf y f g) =
        if find y g is Some v then
          if x == y then Some (f v)
          else find x g
        else None.
Proof.
rewrite /updgf; case: (dom_find y)=>[//|[k v] /In_find H _].
by rewrite findU (In_cond H) (In_valid H).
Qed.

Lemma umfiltUg x f p g :
        um_filter p (updgf x f g) =
        if find x g is Some v then
          if p (x, f v) then upd x (f v) (um_filter p g)
          else free (um_filter p g) x
        else undef.
Proof.
rewrite /updgf.
case: (dom_find x g)=>[//|[k v] /In_find H _].
by rewrite umfiltU ?(In_cond H).
Qed.

Lemma kfiltUg x f p g :
        kfilt (updgf x f g) p =
        if p x then updgf x f (kfilt g p)
        else if x \in nodes g then free (kfilt g p) x
             else undef.
Proof.
rewrite /kfiltx !umfiltUg /updgf find_umfiltk /=.
by case: (p x)=>//; case: (dom_find x g).
Qed.

Lemma InFUg w x f g :
        w \In updgf x f g <->
        if find x g is Some v then
          if w.1 == x then w.2 = f v
          else w \In free g x
        else False.
Proof.
rewrite /updgf.
case: (dom_find x g)=>[_|[k v] /In_find H _].
- by split=>// /In_undef.
rewrite InFU validU (In_cond H) (In_valid H).
by split=>//; case.
Qed.

Lemma InUg w x f g :
        w \In updgf x f g <->
        if find x g is Some v then
          if w.1 == x then w.2 = f v
          else w \In g
        else False.
Proof.
rewrite /updgf.
case: (dom_find x g)=>[_|[k v] /In_find H _].
- by split=>// /In_undef.
rewrite InU validU (In_cond H) (In_valid H).
by split=>//; case.
Qed.

End UpdgLemmas.

(* update contents and linkage, without looking at old ones *)
Abbreviation updg x v g := (updgf x (fun => v) g).
(* update contents while preserving old linkage *)
Abbreviation updgC x a g := (updgf x (fun v => (a, v.2)) g).


(***********)
(* Mapping *)
(***********)

(* modify contents and linkage of each node in the graph *)
(* according to a function *)

Definition graph_map {V : link} {A B} f :
    partial_graph V A -> partial_graph V B :=
  omap (fun x => Some (f x.1 x.2)).

HB.instance Definition _ V A B f :=
  OmapFun.copy (@graph_map V A B f) (graph_map f).
HB.instance Definition _ (V : link) A B f :=
  isMapFun.Build nat nat_pred (A*V)%type (B*V)%type
    (@partial_graph V A) (partial_graph V B)
    (@graph_map V A B f) (fun => is_true_true).

Section GraphMap.
Context {V : link} {A B : Type}.
Implicit Type g : partial_graph V A.
Implicit Type f : node -> A * V -> B * V.

Lemma eq_in_graphmap f1 f2 g :
         (forall k v, (k, v) \In g -> f1 k v = f2 k v) <->
         graph_map f1 g = graph_map f2 g.
Proof. by rewrite -eq_in_omap; split=>[/= H x /H ->|H k v /H []]. Qed.

Lemma graphmap_id (f : node -> A * V -> A * V) g :
        (forall k v, (k, v) \In g -> f k v = v) ->
        graph_map f g = g.
Proof. by move=>H; rewrite omf_some /omfx //= =>-[k v] /H ->. Qed.

(* renaming basic properties for easier search *)

Lemma nodes_graphmap f g : nodes (graph_map f g) = nodes g.
Proof. exact: dom_mf. Qed.

Lemma find_graphmap f g x :
        find x (graph_map f g) =
        if find x g is Some v then Some (f x v) else None.
Proof. exact: find_omf. Qed.

Lemma graphmapPt f x v :
        graph_map f (pts x v) = pts x (f x v).
Proof. exact: mfPt. Qed.

Lemma graphmapPtUn f x v g :
        graph_map f (pts x v \+ g) = pts x (f x v) \+ graph_map f g.
Proof. exact: mfPtUn. Qed.

Lemma graphmapUnPt f x v g :
        graph_map f (g \+ pts x v) = graph_map f g \+ pts x (f x v).
Proof. exact: mfUnPt. Qed.

Lemma graphmapUn f g1 g2 :
        graph_map f (g1 \+ g2) = graph_map f g1 \+ graph_map f g2.
Proof. exact: mfUn. Qed.

Lemma graphmapF f g x : graph_map f (free g x) = free (graph_map f g) x.
Proof. exact: omfF. Qed.

End GraphMap.

(***********)
(* Erasure *)
(***********)

(* erase contents of each node *)
(* that is, map a graph with contents A to *)
(* the graph with contents unit *)
(*  but unmodified linkage *)

Definition erase {V : link} A (g : partial_graph V A) :=
  graph_map (fun _ v => (tt, v.2)) g.
HB.instance Definition _ V A :=
  MapFun.copy (@erase V A) (@erase V A).

Section Erase.
Context {V : link} {A : Type}.
Implicit Type g : partial_graph V A.

Lemma nodes_erase g : nodes (erase g) = nodes g.
Proof. exact: nodes_graphmap. Qed.

Lemma edge_erase g : edge (erase g) =2 edge g.
Proof.
move=>x y; rewrite /edge/erase /= !mem_filter dom_omf_some //=.
by rewrite /adj find_omf; case: (find x g).
Qed.

Lemma find_erase g x :
        find x (erase g) =
        ssrfun.omap (pair tt \o snd) (find x g).
Proof. by exact: find_omf. Qed.

Lemma adj_erase g : adj (erase g) =1 adj g.
Proof. by move=>x; rewrite /adj find_erase; case: (find x g). Qed.

Lemma In_eraseX g x vv :
        (x, vv) \In erase g <->
        exists v, (x, (v, vv.2)) \In g.
Proof.
case: vv; case=>vv; rewrite In_omfX /=; split.
- by case=>[[w1 w2]] H [<-]; exists w1.
by case=>v H; exists (v, vv).
Qed.

Lemma In_erase g x v adj :
        (x, (v, adj)) \In g ->
        (x, (tt, adj)) \In erase g.
Proof. by move=>H; apply/In_eraseX; exists v. Qed.

Lemma In_eraseA g x v :
        (x, (tt, v)) \In erase g <->
        x \in nodes g /\ links v = adj g x.
Proof.
split; first by case/In_eraseX=>a /[dup] /In_dom D /In_graph.
case=>/In_domX [[a w]] /[dup] H /In_graph -> /inj_links ->.
by apply/In_eraseX; exists a.
Qed.

Lemma erase_eq g1 g2 :
        valid g1 ->
        valid g2 ->
        erase g1 = erase g2 <->
        [/\ nodes g1 =i nodes g2 &
            adj g1 =1 adj g2].
Proof.
move=>V1 V2; split=>[E|[En Ea]].
- split; first by rewrite -nodes_erase E nodes_erase.
  by move=>z; rewrite -adj_erase E adj_erase.
apply: umem_eq; rewrite ?pfVE //; case=>k [][xs].
by rewrite !In_eraseA En Ea.
Qed.

Lemma find_erase_eq g1 g2 x :
        find x (erase g1) = find x (erase g2) <->
        ssrfun.omap snd (find x g1) = ssrfun.omap snd (find x g2).
Proof.
rewrite !find_erase /ssrfun.omap/obind/oapp.
case: (find x g1); case: (find x g2)=>//= a1 a2.
by split; case=>->.
Qed.

Lemma kfilt_erase g p : kfilt (erase g) p = erase (kfilt g p).
Proof. by rewrite umfiltk_omf. Qed.

Lemma erase_kfilt g p : erase (kfilt g p) = kfilt (erase g) p.
Proof. by rewrite umfiltk_omf. Qed.

Lemma erase_id (g : partial_graph V unit) : erase g = g.
Proof. by rewrite omf_some //; case=>k [[]]. Qed.

Lemma erasePt x (v : A) (xs : seq node) :
        erase (pts x (v, xs)) = pts x (tt, xs).
Proof. exact: mfPt. Qed.

Lemma erasePtUn x v xs g :
        erase (pts x (v, xs) \+ g) = pts x (tt, xs) \+ erase g.
Proof. exact: mfPtUn. Qed.

Lemma eraseUn g1 g2 :
        erase (g1 \+ g2) = erase g1 \+ erase g2.
Proof. exact: mfUn. Qed.

Lemma eraseF g x : erase (free g x) = free (erase g) x.
Proof. exact: omfF. Qed.

End Erase.

(*********)
(* Sinks *)
(*********)

(* list of nodes that have an incoming edge *)
(* includes target nodes of dangling edges *)

Definition sinks {V : link} {A} (g : partial_graph V A) : seq node :=
  flatten (map (links \o snd) (range g)).

Section Sinks.
Context {V : link} {A : Type}.
Implicit Type g : partial_graph V A.

Lemma sinks_bigadj g :
        sinks g =i \big[cat/[::]]_(x <- nodes g) (adj g x).
Proof.
move=>x; rewrite /sinks/adj flatten_map_big assocs_dom !big_map.
by congr (x \in _); apply: eq_Bigr=>-[k v] /In_assocs/In_find ->.
Qed.

(* sinks with property that x \in nodes g *)
Lemma sinksP g y :
        reflect (exists2 x, x \in nodes g & y \in adj g x)
                (y \in sinks g).
Proof. by rewrite sinks_bigadj big_cat_mem_has; apply: hasP. Qed.

(* version without x \in nodes g *)
Lemma sinksPA g y :
        reflect (exists x, y \in adj g x) (y \in sinks g).
Proof.
apply: (iffP (sinksP g y)); first by case=>x Dx Ay; exists x.
by case=>x Ay; exists x=>//; apply: adjD Ay.
Qed.

Lemma sinks_undef : sinks (undef : partial_graph V A) = [::].
Proof. by []. Qed.

Lemma sinks_unit : sinks (Unit : partial_graph V A) = [::].
Proof. by []. Qed.

Lemma sinksPt x (v : A * V) :
        sinks (pts x v) = if x != null then links v.2 else [::].
Proof. by case: eqVneq=>[->//|N]; rewrite /sinks rangePtK //= cats0. Qed.

Lemma sinksUn g1 g2 :
        valid (g1 \+ g2) ->
        sinks (g1 \+ g2) =i sinks g1 ++ sinks g2.
Proof.
move=>W /= x; rewrite mem_cat; case: flattenP=>/= H; apply/esym.
- case: H=>_ /mapPP [v ->] /In_rangeX [k] /InUn [] H /= X;
  apply/orP; [left|right]; apply/flattenP=>//=; exists (links v.2)=>//; 
  by apply/mapPP; exists v=>//; apply: In_range H.
by apply: contra_notF H; case/orP=>/flattenP [_] /mapPP [v -> H /= X];
exists (links v.2)=>//; apply/mapPP; exists v=>//;
[apply: In_rangeL H|apply: In_rangeR H].
Qed.

Lemma sinksUnE g1 g2 x :
        valid (g1 \+ g2) ->
        (x \in sinks (g1 \+ g2)) = (x \in sinks g1) || (x \in sinks g2).
Proof. by rewrite -mem_cat=>/sinksUn ->. Qed.

Lemma sinksPtUn x (v : A * V) g :
        valid (pts x v \+ g) ->
        sinks (pts x v \+ g) =i links v.2 ++ sinks g.
Proof. by move=>W a; rewrite sinksUn // sinksPt (validPtUn_cond W). Qed.

Lemma sinksPtUnK x (v : A * V) g :
        valid (pts x v \+ g) ->
        path ord x (nodes g) ->
        sinks (pts x v \+ g) = links v.2 ++ sinks g.
Proof. by move=>W /(order_path_min trans) P; rewrite /sinks rangePtUnK. Qed.

Lemma sinksV g x :
        x \in sinks g ->
        valid g.
Proof. by move/sinksP=>[y] /dom_valid. Qed.

Lemma adj_sinks_sub g x : {subset adj g x <= sinks g}.
Proof. by move=>y X; apply/sinksPA; exists x. Qed.

End Sinks.

Section Sinks2.
Context {V : link} {A : Type}.
Implicit Type g : partial_graph V A.

Lemma sinks_erase g : sinks (erase g) = sinks g.
Proof.
elim/um_indf: g=>[||k [v xs] g IH W P].
- by rewrite pfundef.
- by rewrite pfunit.
rewrite erasePtUn !sinksPtUnK ?IH //.
- by rewrite -(erasePtUn k v xs) pfVE.
by rewrite nodes_erase.
Qed.

Lemma sinks_kfilt_sub {g} {p} : {subset sinks (kfilt g p) <= sinks g}.
Proof.
case: (normalP g)=>[->|W x S]; first by rewrite pfundef.
by rewrite (kfiltC g p) in W *; rewrite sinksUnE // S.
Qed.

Lemma sinks_free_sub {g} {x} : {subset sinks (free g x) <= sinks g}.
Proof.
move=>y; have [|Nx] := boolP (x \in nodes g); last by rewrite freeND.
case/um_eta=>kv [/In_find/In_valid W E] S.
by rewrite E in W *; rewrite sinksUnE // S orbT.
Qed.

End Sinks2.

(**********)
(* Leaves *)
(**********)

(* leaf is a node with only null successors, if any *)

Definition leaves {V : link} {A} (g : partial_graph V A) : seq node :=
  filter (fun y => all (eq_op^~ null) (adj g y)) (nodes g).

Lemma leavesE {V : link} {A} (g : partial_graph V A) x :
         (x \in leaves g) =
         (x \in nodes g) && all (fun x => x == null) (adj g x).
Proof. by rewrite mem_filter andbC. Qed.

Lemma leavesP {V : link} {A} (g : partial_graph V A) x :
        reflect (x \in nodes g /\
                 {in adj g x, forall x, x == null})
                (x \in leaves g).
Proof. by rewrite leavesE; apply: (iffP andP); case=>-> /allP. Qed.

Lemma leavesD {V : link} {A} {g : partial_graph V A} :
        {subset leaves g <= nodes g}.
Proof. by move=>x; rewrite mem_filter=>/andP []. Qed.

Lemma leavesUn {V : link} {A} (g1 g2 : partial_graph V A) x :
        valid (g1 \+ g2) ->
        (x \in leaves (g1 \+ g2)) = (x \in leaves g1) || (x \in leaves g2).
Proof.
move=>W; rewrite !leavesE domUnE // adjUnL //.
by case D: (x \in dom g1)=>//=; rewrite (negbTE (dom_inNL W D)) orbF.
Qed.

(*********)
(* loops *)
(*********)

(* loop is a cycle of size 1 *)

Definition loops {V : link} {A} (g : partial_graph V A) : seq node :=
  nodes (kfilt g (fun x => x \in adj g x)).

Section LoopsLemmas.
Context {V : link} {A : Type}.
Implicit Type g : partial_graph V A.

Lemma loopsE g x :
        (x \in loops g) = (x \in nodes g) && (x \in adj g x).
Proof. exact: nodes_kfilt. Qed.

Lemma In_loopsP g x :
        reflect (exists v xs, (x, (v, xs)) \In g /\ x \in links xs)
                (x \in loops g).
Proof.
apply: (iffP (In_nodes_kfiltX g _ x));
by case=>v [xs][/[dup]/In_graph ->]; exists v, xs.
Qed.

Lemma loopsD {g} : {subset loops g <= nodes g}.
Proof. by move=>x; rewrite loopsE=>/andP []. Qed.

Lemma disj_loopsR g1 g2 :
        valid (g1 \+ g2) ->
        disjoint (nodes g1) (loops g2).
Proof. by move=>W; apply/disjoint_subL/disjointD/W/loopsD. Qed.

Lemma disj_loopsL g1 g2 :
        valid (g1 \+ g2) ->
        disjoint (nodes g2) (loops g1).
Proof. by rewrite joinC; apply/disj_loopsR. Qed.

Lemma loopsUn g1 g2 x :
        valid (g1 \+ g2) ->
        (x \in loops (g1 \+ g2)) = (x \in loops g1) || (x \in loops g2).
Proof.
move=>W; rewrite !loopsE domUnE // adjUnL //.
by case D: (x \in dom g1)=>//=; rewrite (negbTE (dom_inNL W D)) orbF.
Qed.

End LoopsLemmas.


(****************)
(* Reachability *)
(****************)

(* given node x, list of nodes connected to x *)

Definition reach {V : link} A (g : partial_graph V A) x :=
  dfs g (size (nodes g)) [::] x.

(***************************)
(* reach in terms of paths *)
(***************************)

Section ReachPath.
Context {V : link} {A : Type}.
Implicit Type g : partial_graph V A.

Lemma reachP g x y :
        reflect [/\ x \in nodes g & exists xs,
                     path (edge g) x xs /\ y = last x xs]
                (y \in reach g x).
Proof.
rewrite /reach /=.
case: (boolP (x \in nodes g))=>Dx; last first.
- by move/dfs_notin: Dx=>->; constructor; case.
apply: (iffP (dfs_pathP _ _ _ _ _))=>//.
- by case=>xs P E /disjoint_consRE [_] D; split=>//; exists xs.
by case=>_ [xs][P E]; exists xs=>//; apply/allP.
Qed.

(* there's path from x to y with no duplicates *)
Lemma reachX g x y :
        reflect [/\ x \in nodes g & exists xs,
                [/\ path (edge g) x xs, y = last x xs &
                    uniq (x :: xs)]]
          (y \in reach g x).
Proof.
case: reachP=>H; constructor; last first.
- by case=>Dx [xs][Px E _]; apply: H; split=>//; exists xs.
case: H=>Dx [xs][Px Ey]; split=>//.
by case/shortenP: Px Ey=>xs' Px U S Ey; exists xs'.
Qed.

(* alternative characterization of reach *)
Lemma reachEA g x y :
        (y \in reach g x) =
        if x \in nodes g then
          (y == x) || has (fun i => y \in reach (free g x) i) (adj g x)
        else false.
Proof.
apply/idP/idP.
- case/reachX=>Dx [[|z xs]][/=]; rewrite Dx ?inE ?negb_or.
  - by move=>_ -> _; rewrite eqxx.
  case/andP=>Eg P E /andP [/andP [Nxz Nx]] /andP [Nz U].
  have Nzxs : x \notin z :: xs by rewrite inE negb_or Nxz Nx.
  apply/orP; right; apply/hasP; exists z; first by rewrite edgeA.
  apply/reachP; split; first by rewrite domF eq_sym (negbTE Nxz) (edgeD Eg).
  by exists xs; rewrite -(eq_in_path (edge_free_eq g Nzxs)).
move=>N; apply/reachP; case: ifP N=>// Dx /orP [/eqP ->|N];
split=>//; first by exists [::].
case/hasP: N=>z Az /reachP []; rewrite domF eq_sym.
case: (x =P z)=>//= /eqP Nxz Dz [xs][] /shortenP [xs' P U _ E].
move: (path_nodes P)=>P1; have Nz : x \notin z :: xs'.
- by rewrite inE negb_or Nxz (contra (P1 _)) // domF eqxx.
by exists (z :: xs'); rewrite /= adj_edge //= (eq_in_path (edge_free_eq g Nz)).
Qed.

(* tighter alternative using children instead of adj *)
Lemma reachE g x y :
        (y \in reach g x) =
        if x \in nodes g then
          (y == x) || has (fun i => y \in reach (free g x) i) (children g x)
        else false.
Proof.
rewrite reachEA; case: ifP=>// Dx; case: (y =P x)=>//= /eqP Nyx.
apply/hasP/hasP; case=>z Eg H; exists z=>//; last first.
- by rewrite -edge_children in Eg; rewrite edgeA.
rewrite -edge_children adj_edge //.
by case/reachP: H; rewrite domF; case: eqP.
Qed.

(* restatement via membership *)

Lemma reachEAX g x :
        reach g x =i
        if x \in nodes g then
          [predU pred1 x & \big[cat/[::]]_(i <- adj g x) reach (free g x) i]
        else pred0.
Proof. by move=>y; rewrite 2!fun_if inE big_cat_mem_has -reachEA. Qed.

Lemma reachEX g x :
        reach g x =i
        if x \in nodes g then
          [predU pred1 x & \big[cat/[::]]_(i <- children g x) reach (free g x) i]
        else pred0.
Proof. by move=>y; rewrite 2!fun_if inE big_cat_mem_has -reachE. Qed.

End ReachPath.

(***************************)
(* reach structural lemmas *)
(***************************)

Section ReachStructurals.
Context {V : link} {A : Type}.
Implicit Type g : partial_graph V A.

Lemma reach_undef x : reach (undef : partial_graph V A) x = [::].
Proof. by apply: eqnil=>y; apply/reachP; case; rewrite nodes_undef. Qed.

Lemma reach_unit x : reach (Unit : partial_graph V A) x = [::].
Proof. by apply: eqnil=>y; apply/reachP; case; rewrite nodes_unit. Qed.

Lemma reachV g x y :
        y \in reach g x ->
        valid g.
Proof. by case: (normalP g)=>[->|//]; rewrite reach_undef. Qed.

Lemma reachD g x y :
        y \in reach g x ->
        (x \in nodes g) * (y \in nodes g).
Proof.
case/reachP=>Dx [xs][P E].
have : y \in x :: xs by rewrite E mem_last.
rewrite inE; case/orP=>[/eqP ->//|Dy].
by rewrite Dx (path_nodes P Dy).
Qed.

Lemma reachD1 g x y :
        y \in reach g x ->
        x \in nodes g.
Proof. by case/reachD. Qed.

Lemma reachD2 g x y :
        y \in reach g x ->
        y \in nodes g.
Proof. by case/reachD. Qed.

Lemma reachD_kfilt g p x y :
        y \in reach (kfilt g p) x ->
        (x \in nodes g) * (y \in nodes g) * (x \in p) * (y \in p).
Proof.
by move/reachD; rewrite !nodes_kfilt; case=>/andP [->->] /andP [->->].
Qed.

Lemma reachDN g x :
        x \notin nodes g ->
        reach g x = [::].
Proof. by move/negP=>D; apply/eqnil=>y; apply/reachP; case. Qed.

Lemma reachDN_kfilt g (p : pred node) x :
        x \notin p ->
        reach (kfilt g p) x = [::].
Proof.
move/negP=>Px; apply/eqnil=>y; apply/reachP; case.
by rewrite nodes_kfilt; case/andP.
Qed.

Lemma reach0 g x : (x \in reach g x) = (x \in nodes g).
Proof. by apply/reachP/idP; [case|split=>//; exists [::]]. Qed.

Lemma reach0I g x :
        x \in nodes g ->
        x \in reach g x.
Proof. by rewrite reach0=>->. Qed.

Lemma reach0N g x y :
        x \in nodes g ->
        y \notin reach g x ->
        x != y.
Proof. by move=>Gx; apply: contra=>/eqP <-; rewrite reach0 Gx. Qed.

Lemma reach_trans g : transitive (fun x y => y \in reach g x).
Proof.
move=>x y z /reachP [Dy][ys][Py Ey].
case/reachP=>Dx [xs][Px Ex]; apply/reachP.
split=>//; exists (ys ++ xs); split.
- by rewrite cat_path -Ey Py Px.
by rewrite last_cat -Ey.
Qed.

Lemma uniq_reach g x : uniq (reach g x).
Proof. exact: uniq_dfs. Qed.

(* reach depends only on graph erasure, not on contents *)

Lemma reach_erase g x : reach (erase g) x =i reach g x.
Proof.
move=>y; apply/reachP/reachP; rewrite nodes_erase;
case=>Dx [xs][Px Ey]; split=>//; exists xs.
- by rewrite -(eq_path (edge_erase g)).
by rewrite (eq_path (edge_erase g)).
Qed.

(* reachby and union *)

Lemma reachUn g1 g2 x :
        [pcm g1 <= g2] ->
        valid g2 ->
        {subset reach g1 x <= reach g2 x}.
Proof.
case=>g -> W y /reachP [Dx][xs][Px Ey].
apply/reachP; split=>//; first by rewrite domUn inE W Dx.
by exists xs; split=>//; apply: sub_path Px=>z w; apply: edgeUnL.
Qed.

Lemma reachUnL g1 g2 x :
        valid (g1 \+ g2) ->
        {subset reach g1 x <= reach (g1 \+ g2) x}.
Proof. by apply: reachUn. Qed.

Lemma reachUnR g1 g2 x :
        valid (g1 \+ g2) ->
        {subset reach g2 x <= reach (g1 \+ g2) x}.
Proof. by apply: reachUn. Qed.

Lemma reachF g k x :
        {subset reach (free g k) x <= reach g x}.
Proof.
case: (normalP g)=>[->|W]; first by rewrite free_undef.
by apply: reachUn (pleq_free _ _) W.
Qed.

(* reach monotonicity *)

Lemma reach_kfilt_sub g (p : pred node) x :
        {subset reach (kfilt g p) x <= reach g x}.
Proof.
case: (normalP g)=>[->|W y H]; first by rewrite pfundef.
by rewrite (kfiltC g p) reachUnL // -kfiltC.
Qed.

Lemma reach_kfilt_mono g (p1 p2 : pred node) x :
        {subset p1 <= p2} ->
        {subset reach (kfilt g p1) x <= reach (kfilt g p2) x}.
Proof.
case: (normalP g)=>[->|W S]; first by rewrite !pfundef.
rewrite (kfilt_predD g S); apply: reachUn=>//.
by rewrite valid_umfiltkUn // => z _ /= ->.
Qed.

Lemma reach_kfilt_eq g (p1 p2 : pred node) x :
        p1 =i p2 ->
        reach (kfilt g p1) x =i reach (kfilt g p2) x.
Proof.
by move=>S y; apply/idP/idP; apply/reach_kfilt_mono=>z; rewrite S.
Qed.

(* relativized versions of reach_mono and reach_eq *)

Lemma reach_kfilt_in_mono g p1 p2 x :
        {in nodes g, {subset p1 <= p2}} ->
        {subset reach (kfilt g p1) x <= reach (kfilt g p2) x}.
Proof.
move=>S y; rewrite kfilt_nodesI=>R; rewrite kfilt_nodesI.
apply: reach_kfilt_mono R=>z; rewrite !inE.
by case Dz : (z \in nodes g)=>//=; apply: S Dz.
Qed.

Lemma reach_kfilt_in_eq g p1 p2 x :
        {in nodes g, p1 =i p2} ->
        reach (kfilt g p1) x =i reach (kfilt g p2) x.
Proof.
by move=>S y; apply/idP/idP; apply: reach_kfilt_in_mono=>z Z; rewrite S.
Qed.

(* reach equality for two different graphs *)
(* reaches are equal if erasures are equal *)

Lemma eq_reach g1 g2 x :
        nodes g1 =i nodes g2 ->
        (forall x, adj g1 x = adj g2 x) ->
        reach g1 x =i reach g2 x.
Proof.
case: (normalP g1)=>[->|V1]; case: (normalP g2)=>[->|V2] //.
- move=>En Ea z; rewrite reach_undef; apply/esym/reachP.
  by case; rewrite -En dom_undef.
- move=>En Ea z; rewrite reach_undef; apply/reachP.
  by case; rewrite En dom_undef.
by move=>En Ea z; rewrite -reach_erase (_ : erase g1 = erase g2)
?reach_erase // erase_eq.
Qed.

(* some alternatives *)

Lemma eq_reach2 g1 g2 x :
        find^~ (erase g1) =1 find^~ (erase g2) ->
        reach g1 x =i reach g2 x.
Proof.
move=>H; apply: eq_reach=>z; move: (H z); rewrite !find_erase /adj;
by case: (dom_find z g1); case: (dom_find z g2)=>//= ?????? [->].
Qed.

Lemma eq_reach3 g1 g2 x :
        ssrfun.omap snd \o find^~ g1 =1 ssrfun.omap snd \o find^~ g2 ->
        reach g1 x =i reach g2 x.
Proof. by move=>H; apply: eq_reach2=>z; rewrite find_erase_eq; apply: H. Qed.

(* relativized versions *)

Lemma eq_in_reach g1 g2 (p : pred node) x :
        {in p, nodes g1 =i nodes g2} ->
        {in p, adj g1 =1 adj g2} ->
        reach (kfilt g1 p) x =i reach (kfilt g2 p) x.
Proof.
move=>En Ea; apply: eq_reach=>z.
- rewrite !nodes_kfilt -!(andbC (z \in p)).
  by case Z: (z \in p)=>//=; rewrite En.
by rewrite !adj_kfilt; case: ifP=>// Z; rewrite Ea.
Qed.

Lemma eq_in_reach2 g1 g2 (p : pred node) x :
        {in p, find^~ (erase g1) =1 find^~ (erase g2)} ->
        reach (kfilt g1 p) x =i reach (kfilt g2 p) x.
Proof.
move=>H; apply: eq_reach2=>z; rewrite !erase_kfilt !find_kfilt.
by case: ifP=>// /H.
Qed.

Lemma eq_in_reach3 g1 g2 (p : pred node) x :
        {in p, ssrfun.omap snd \o find^~ g1 =1 ssrfun.omap snd \o find^~ g2} ->
        reach (kfilt g1 p) x =i reach (kfilt g2 p) x.
Proof. by move=>H; apply: eq_in_reach2=>z /H; rewrite find_erase_eq. Qed.

End ReachStructurals.

(********************************)
(* (de)constructing reach paths *)
(********************************)

Section ReachPathSurgery.
Context {V : link} {A : Type}.
Implicit Type g : partial_graph V A.

(* deconstructing connecting path from the beginning *)
Lemma edge_reachX g x y :
        y != x ->
        y \in reach g x ->
        exists2 z, edge g x z & y \in reach (free g x) z.
Proof.
move=>Nxy; rewrite reachE (negbTE Nxy) /=.
by case: ifP=>// Dx /hasP [z Az H]; exists z.
Qed.

(* weakened variant *)
Lemma edge_reach g x y :
        y != x ->
        y \in reach g x ->
        exists2 z, edge g x z & y \in reach g z.
Proof.
by move=>Nxy /(edge_reachX Nxy) [z Eg H]; exists z=>//; apply/reachF/H.
Qed.

(* deconstructing connecting path from the end *)
Lemma reach_edgeX g x y :
        y != x ->
        y \in reach g x ->
        exists2 z, z \in reach (free g y) x & edge g z y.
Proof.
move/eqP=>Nxy /reachX [D][xs] /=.
case: {xs}(lastP xs)=>[|xs z][/[swap]]; first by move/Nxy.
rewrite last_rcons=><-; rewrite rcons_path=>/andP [Pxs Pz].
rewrite rcons_uniq mem_rcons inE negb_or -andbA.
case/and4P=>N1 N2 N3 N4; exists (last x xs)=>//.
apply/reachP; split; first by rewrite domF (negbTE N1).
exists xs; split=>//.
have N : y \notin x :: xs by rewrite inE negb_or eq_sym N1 N3.
by rewrite -(eq_in_path (edge_free_eq g N)).
Qed.

(* weakened variant *)
Lemma reach_edge g x y :
        y != x ->
        y \in reach g x ->
        exists2 z, z \in reach g x & edge g z y.
Proof.
by move=>Nxy /(reach_edgeX Nxy) [z H Eg]; exists z=>//; apply/reachF/H.
Qed.

(* extending connecting path from the beginning *)
Lemma edge_reachI g x y z :
        edge g x y ->
        z \in reach g y ->
        z \in reach g x.
Proof.
move=>Eg /reachP [Dy][ys][Py Ez]; apply/reachP.
split=>//; first by rewrite (edgeD Eg).
by exists (y::ys); split=>//=; rewrite Eg Py.
Qed.

(* extending connecting path from the end *)
Lemma reach_edgeI g x y z :
        y \in reach g x ->
        edge g y z ->
        z \in reach g x.
Proof.
case/reachP=>Dx [xs][Px Ey] Eg; apply/reachP; split=>//.
by exists (rcons xs z); rewrite rcons_path last_rcons -Ey Px Eg.
Qed.

(* if y reachable from x, then anything reachable from x *)
(* can be reached by y-free path, or is otherwise itself *)
(* reachable from y *)
Lemma reach_in {g x} y :
        y \in reach g x ->
        reach g x =i [predU reach (free g y) x & reach g y].
Proof.
move=>Ry z; rewrite inE; apply/idP/idP; last first.
- by case/orP=>[/reachF|/(reach_trans Ry)].
case/reachP=>Dx [xs][P E].
have [Nx|Mx] := boolP (y \in x :: xs); last first.
(* if y isn't in the path, choose left *)
- move: (Mx); rewrite inE negb_or; case/andP=>Mx1 _.
  apply/orP; left; apply/reachP; split.
  - by rewrite domF eq_sym (negbTE Mx1).
  by exists xs; rewrite -(eq_in_path (edge_free_eq g Mx)).
(* if y in the path, then z reachable from y; choose right *)
case/splitPl: Nx P E=>/= p1 p2 Ey.
rewrite cat_path last_cat {}Ey=>/andP [_ P] E.
apply/orP; right; apply/reachP.
by split; [rewrite (reachD Ry)|exists p2].
Qed.

(* if y not reachable from x, then removing y from g *)
(* doesn't change reachability from x *)
Lemma reach_notin {g x} y :
        y \notin reach g x ->
        reach g x =i reach (free g y) x.
Proof.
move=>Ry z; apply/idP/idP; last by apply: reachF.
case/reachP=>Dx [xs][P E].
have [Nx|Mx] := boolP (y \in x :: xs); last first.
(* if y isn't in the path, trivial *)
- move: (Mx); rewrite inE negb_or; case/andP=>Mx1 _.
  apply/reachP; split=>//; first by rewrite domF eq_sym (negbTE Mx1).
  by exists xs; rewrite -(eq_in_path (edge_free_eq g Mx)).
(* otherwise suffices to show that y reachable from x to contradict Ry *)
suff : y \in reach g x by rewrite (negbTE Ry).
(* split the path at y *)
case/splitPl: Nx {E} P=>/= p1 p2 Ey.
rewrite cat_path; case/andP=>P _.
by apply/reachP; split=>//; exists p1.
Qed.

(* putting the above two lemmas together *)
Lemma reach_mem {g x} y z :
        (z \in reach g x) =
        if y \in reach g x then
          (z \in reach (free g y) x) || (z \in reach g y)
        else z \in reach (free g y) x.
Proof. by case: ifPn=>Y; [apply: reach_in|apply: reach_notin]. Qed.

(* if y is reachable from x, but not from x', then *)
(* y is reachable from x by a path that avoids whole *)
(* subcomponent of x' *)
Lemma reach_avoid g x x' y :
        y \notin reach g x' ->
        (y \in reach g x) =
        (y \in reach (kfilt g [predC reach g x']) x).
Proof.
move=>Ny; apply/idP/idP; last by move/reach_kfilt_sub.
case/reachP=>Dx [xs][Px Ey].
have [Nx|Mx] := boolP (has [in reach g x'] (x :: xs)); last first.
(* if path contains no nodes reachable from x', trivial *)
- move/hasPn: Mx=>/= Mx; apply/reachP; split.
  - by rewrite nodes_kfilt !inE Dx Mx // inE eqxx.
  exists xs; split=>//.
  by apply/(sub_in_path edge_kfilt_in_sub)/Px/allP.
(* if path contains node z reachable from x' *)
(* (we pick last such z, but it doesn't matter) *)
case: {-1} _ _ _ / {Nx} (split_findlast Nx) (erefl (x::xs)).
move=>/= z p1 p2=>Rz _ X.
(* suffices to show that y is reachable from z *)
(* because then y is also reachable from x'; contradiction *)
suff Ry : y \in reach g z by rewrite (reach_trans Rz Ry) in Ny.
case: p1 X Ey Px=>[[<- _]|b p1 [_ ->]] /= Ey Px.
- by apply/reachP; split=>//; exists xs.
rewrite cat_path last_cat last_rcons rcons_path -andbA in Ey Px.
case/and3P: Px=>_ Ea Pz; apply/reachP; rewrite (reachD Rz).
by split=>//; exists p2.
Qed.

Lemma reach_avoid1 {g x x'} y :
        y \notin reach g x' ->
        (y \in reach g x) = (y \in reach (free g x') x).
Proof. by move=>Y; rewrite (reach_mem x') (negbTE Y) orbF if_same. Qed.

(* reachability out of x for the reachable subgraph *)
(* equals reachability out of x for the graph *)
Lemma reach_reach g x :
        reach (kfilt g [in reach g x]) x =i reach g x.
Proof.
move=>y; apply/idP/idP; case/reachP.
- rewrite nodes_kfilt=>/andP [Dx Rx][xs][Px Ey].
  apply/reachP; split=>//; exists xs; split=>//.
  by apply/sub_path/Px=>a b; rewrite edge_kfilt; case/and3P.
move=>Dx [xs][Px Ey]; apply/reachP; split.
- by rewrite nodes_kfilt reach0 Dx.
exists xs; split=>//; apply/(sub_in_path edge_kfilt_in_sub)/Px.
apply/allP=>z; rewrite inE; case/orP=>[/eqP ->|Hz].
- by rewrite reach0.
case/splitPr: Hz Px=>xs1 xs2.
rewrite -cat1s catA cats1 cat_path=>/andP [Px _].
by apply/reachP; split=>//; exists (rcons xs1 z); rewrite last_rcons.
Qed.

Lemma nodes_reach g x :
        nodes (kfilt g [in reach g x]) =i reach g x.
Proof.
move=>z; rewrite nodes_kfilt; case D: (z \in _)=>//=.
by apply/esym/negP=>/reachD2; rewrite D.
Qed.

Lemma path_reach_sub g x xs :
        path (edge g) x xs ->
        {subset xs <= reach g x}.
Proof.
case: xs=>[|y xs] // /[dup]/path_nodes0 D + z Z; case/splitPr: Z=>p q.
rewrite cat_path /=; case/and3P=>E1 E2 _; apply/reachP; split=>//.
by exists (rcons p z); rewrite rcons_path last_rcons E1 E2.
Qed.

End ReachPathSurgery.

(******************)
(* Bireachability *)
(******************)

(* y is bireachable from x iff *)
(* x and y are mutually reachable *)
(* (symmetric closure of reach) *)
(* Thus, x-y-x is a loop (also y-x-y) *)

Definition bireach {V : link} A (g : partial_graph V A) x : seq node :=
  filter (fun y => x \in reach g y) (reach g x).

Section BireachLemmas.
Context {V : link} {A : Type}.
Implicit Type g : partial_graph V A.

Lemma bireach_sym g x y :
        (x \in bireach g y) = (y \in bireach g x).
Proof. by rewrite !mem_filter andbC. Qed.

Lemma bireach_symE g x y :
        x \in bireach g y -> y \in bireach g x.
Proof. by rewrite bireach_sym. Qed.

Lemma bireach0 g x :
        (x \in bireach g x) = (x \in nodes g).
Proof. by rewrite mem_filter reach0 andbb. Qed.

Lemma bireach0I g x :
        x \in nodes g ->
        x \in bireach g x.
Proof. by rewrite bireach0. Qed.

Lemma bireach0N g x y :
        x \in nodes g ->
        y \notin bireach g x ->
        x != y.
Proof. by move=>Gx; apply: contra=>/eqP <-; rewrite bireach0 Gx. Qed.

Lemma bireach_trans g : transitive (fun x y => y \in bireach g x).
Proof.
move=>x y z; rewrite !mem_filter.
case/andP=>Hyx Hxy /andP [Hxz Hzx].
by rewrite (reach_trans Hxz Hyx) (reach_trans Hxy Hzx).
Qed.

Lemma bireachUn g1 g2 x :
        [pcm g1 <= g2] ->
        valid g2 ->
        {subset bireach g1 x <= bireach g2 x}.
Proof.
move=>H W y; rewrite !mem_filter; case/andP=>[Rx Ry].
by apply/andP; split; apply: (reachUn H).
Qed.

Lemma bireachUnL g1 g2 x :
        valid (g1 \+ g2) ->
        {subset bireach g1 x <= bireach (g1 \+ g2) x}.
Proof. by apply: bireachUn. Qed.

Lemma bireachUnR g1 g2 x :
        valid (g1 \+ g2) ->
        {subset bireach g2 x <= bireach (g1 \+ g2) x}.
Proof. by apply: bireachUn. Qed.

Lemma bireach_kfilt_mono g (p1 p2 : pred node) (x : node) :
        {subset p1 <= p2} ->
        {subset bireach (kfilt g p1) x <= bireach (kfilt g p2) x}.
Proof.
move=>S y; rewrite !mem_filter; case/andP.
by do 2![move/(reach_kfilt_mono S)=>->].
Qed.

Lemma bireach_kfilt_eq g (p1 p2 : pred node) (x : node) :
        p1 =i p2 ->
        bireach (kfilt g p1) x =i bireach (kfilt g p2) x.
Proof. by move=>S y; rewrite !mem_filter !(reach_kfilt_eq g _ S). Qed.

End BireachLemmas.

(*********)
(* Cycle *)
(*********)

Section CycleLemmas.
Context {V : link} {A : Type}.
Implicit Type g : partial_graph V A.

(* elements in a cycle are mutually reachable *)
(* using cycle elements only *)
Lemma reach_cycle_kfilt g xs :
        cycle (edge g) xs ->
        {in xs &, forall x y, y \in reach (kfilt g [in xs]) x}.
Proof.
move=>C x y /rot_to [i q Hr]; rewrite -(mem_rot i) Hr => Hy.
have Hx : x \in xs by rewrite -(mem_rot i) Hr inE eqxx.
have /= Hp1: cycle (edge g) (x :: q) by rewrite -Hr rot_cycle.
have Dx : x \in dom g.
- by move: Hp1; rewrite rcons_path=>/andP [_ /edgeD][].
case/splitPl: Hy Hp1 Hr=>r s Ey.
rewrite rcons_cat cat_path=>/andP [Hxr].
rewrite Ey rcons_path; case/andP=>Hlx /= Ex Hr.
apply/reachP; split=>//; first by rewrite nodes_kfilt Dx Hx.
exists r; split=>//; apply/(sub_in_path edge_kfilt_in_sub)/Hxr.
by apply/allP=>z; rewrite -(mem_rot i xs) Hr !inE mem_cat orbA=>->.
Qed.

(* weakened form *)
Lemma reach_cycle g xs :
        cycle (edge g) xs ->
        {in xs &, forall x y, y \in reach g x}.
Proof. by move=>C x y Hx /(reach_cycle_kfilt C Hx)/reach_kfilt_sub. Qed.

(* elements in a cycle are mutually bi-reachable *)
(* using cycle elements only *)
Lemma bireach_cycle_kfilt g xs :
        cycle (edge g) xs ->
        {in xs &, forall x y, y \in bireach (kfilt g [in xs]) x}.
Proof. by move=>C x y Hx Hy; rewrite mem_filter !(reach_cycle_kfilt C). Qed.

(* weakened form  *)
Lemma bireach_cycle g xs :
        cycle (edge g) xs ->
        {in xs &, forall x y, y \in bireach g x}.
Proof. by move=>C x y Hx Hy; rewrite mem_filter !(reach_cycle C). Qed.

(* characterization of bireach in terms of cycles *)
Lemma bireach_cycleP g x y :
        x != y ->
        reflect (exists2 xs, y \in xs & cycle (edge g) (x :: xs))
                (y \in bireach g x).
Proof.
move=>Nxy; apply/(iffP idP)=>[|[ys Py Cy]]; last first.
- by apply: (bireach_cycle Cy); rewrite inE ?eqxx ?Py ?orbT.
rewrite mem_filter=>/andP [] /reachP [Dy][ys][Py Ex].
elim/last_ind: ys x Py Ex Nxy=>[x _ ->|ys x IH] /=; first by rewrite eqxx.
rewrite rcons_path last_rcons=>_ /andP [Py Ex] -> Nxy.
case/reachP=>Dx [xs][Px Ey]; exists (xs ++ ys).
- have := mem_last x xs.
  by rewrite -Ey inE eq_sym (negbTE Nxy) /= mem_cat=>->.
by rewrite rcons_path cat_path last_cat -Ey Px Py Ex.
Qed.

Lemma bireach_kfilt_cycleP p g x y :
        x != y ->
        reflect (exists xs,
                   [/\ y \in xs, cycle (edge g) (x :: xs) &
                       {subset x :: xs <= p}])
                (y \in bireach (kfilt g p) x).
Proof.
move=>Nxy; apply/(iffP (bireach_cycleP _ Nxy))=>/=.
- case=>xs Dy Px; exists xs; split=>//.
  - by apply/sub_path/Px/edge_kfilt_sub.
  move=>z Z; have : z \in rcons xs x by rewrite mem_rcons.
  by move/(path_nodes Px); rewrite nodes_kfilt; case/andP.
case=>xs [Dy Px S]; exists xs=>//.
apply/(sub_in_path edge_kfilt_in_sub)/Px/allP=>z.
by rewrite inE mem_rcons inE orbA orbb -inE=>/S.
Qed.

Lemma cycle_nodes g xs :
        cycle (edge g) xs ->
        {subset xs <= nodes g}.
Proof. by rewrite (cycle_path null)=>/path_nodes. Qed.

Lemma cycle_edge_free g x ys :
        x \notin ys ->
        cycle (edge g) ys ->
        cycle (edge (free g x)) ys.
Proof.
case: ys=>//= y ys /[dup] N; rewrite inE negb_or=>/andP [Nxy Nys].
rewrite !rcons_path edgeFE Nxy andbT=>/andP [P ->] /=.
by rewrite path_edge_free //=; case: eqP (mem_last y ys) N=>//= <- ->.
Qed.

(* useful renaming *)
Lemma edge_free_cycle g x :
        subpred (cycle (edge (free g x))) (cycle (edge g)).
Proof. exact: (sub_cycle free_edge_sub). Qed.

Lemma loops_cycleE g x : (x \in loops g) = cycle (edge g) [:: x].
Proof. by rewrite /= loopsE edge_adj andbT. Qed.

End CycleLemmas.

(**************)
(* Acyclicity *)
(**************)

(* graph is preacyclic iff *)
(* the only biconnected paths (i.e., loops) are self-loops *)
Definition preacyclic {V : link} A (g : partial_graph V A) :=
  all2rel (fun x y => (y \in bireach g x) ==> (x == y)) (nodes g).

(* graph is acyclic if it doesn't even have self-loops *)
(* (thus, it has no loops of any sort, but this will be proved) *)
Definition acyclic {V : link} A (g : partial_graph V A) :=
  preacyclic g && all (fun x => ~~ edge g x x) (nodes g).

Section AcyclicityLemmas.
Context {V : link} {A : Type}.
Implicit Type g : partial_graph V A.

Lemma preacyclicP g :
        reflect {in nodes g &,
                   forall x y, y \in bireach g x -> x = y}
                (preacyclic g).
Proof.
apply: (iffP idP)=>[|H].
- by move/allrelP=>H x y Dx Dy C; apply/eqP/(implyP _ C)/H.
by apply/allrelP=>x y Dx Dy; apply/implyP=>K; apply/eqP/H.
Qed.

Lemma preacyclic_undef : preacyclic (undef : partial_graph V A).
Proof. by apply/preacyclicP=>x y; rewrite dom_undef. Qed.

Lemma preacyclic_unit : preacyclic (Unit : partial_graph V A).
Proof. by apply/preacyclicP=>x y; rewrite dom0. Qed.

Lemma preacyclicUnSub g1 g2 :
        [pcm g1 <= g2] ->
        valid g2 ->
        preacyclic g2 ->
        preacyclic g1.
Proof.
case=>g -> W /preacyclicP/= H; apply/preacyclicP.
move=>x y Dx Dy C; apply/H/bireachUnL/C=>//;
by rewrite domUn inE W ?Dx ?Dy.
Qed.

Lemma preacyclicUnL g1 g2 :
        valid (g1 \+ g2) ->
        preacyclic (g1 \+ g2) ->
        preacyclic g1.
Proof. by apply: preacyclicUnSub. Qed.

Lemma preacyclicUnR g1 g2 :
        valid (g1 \+ g2) ->
        preacyclic (g1 \+ g2) ->
        preacyclic g2.
Proof. by apply: preacyclicUnSub. Qed.

Lemma acyclicUn g1 g2 :
        [pcm g1 <= g2] ->
        valid g2 ->
        acyclic g2 ->
        acyclic g1.
Proof.
case=>g -> W /andP [Hp /allP /= Ha].
apply/andP; split; first by apply: preacyclicUnL Hp.
apply/allP=>x Dx; apply: contra (edgeUnL W) (Ha x _).
by rewrite domUn inE W Dx.
Qed.

Lemma acyclicUnL g1 g2 :
        valid (g1 \+ g2) ->
        acyclic (g1 \+ g2) ->
        acyclic g1.
Proof. by apply: acyclicUn. Qed.

Lemma acyclicUnR g1 g2 :
        valid (g1 \+ g2) ->
        acyclic (g1 \+ g2) ->
        acyclic g2.
Proof. by apply: acyclicUn. Qed.

(* graph is acyclic iff has no cycles *)

Lemma acyclic_cycleP g :
        reflect (forall x xs, x \in nodes g ->
                   ~~ cycle (edge g) (x :: xs))
                (acyclic g).
Proof.
apply: (iffP idP)=>[|H]; last first.
- apply/andP; split; last first.
  - by apply/allP=>x Dx; apply: contra (H _ [::] Dx); rewrite /= =>->.
  apply/preacyclicP=>x y Dx Dy By; apply/eqP/(contraLR _ By)=>{By} Nxy.
  by apply/(bireach_cycleP _ Nxy); case=>/= xs Hx; apply/negP/H/Dx.
case/andP=>/preacyclicP Ng /allP Ne x xs Dx /=.
rewrite rcons_path; apply/negP=>/andP [].
case: xs=>[_|y xs /= /andP [Exy Px]]; first by apply/negP/Ne.
have Dy : y \in nodes g by rewrite (edgeD Exy).
have : y \notin bireach g x.
- by apply: contraL Exy=>/(Ng x y Dx Dy) <-; apply: Ne Dx.
apply: contraNnot=>Ex; apply: (bireach_cycle (xs:=x::y::xs))=>/=.
- by rewrite Exy rcons_path Px Ex.
- by rewrite inE eqxx.
by rewrite !inE eqxx orbT.
Qed.

Lemma acyclic_adj g x :
        acyclic g ->
        x \notin adj g x.
Proof.
case/andP=>_ /allP H.
have [Dx|Nx] := boolP (x \in nodes g); last by rewrite adjND.
by apply: contra (H _ Dx)=>Lx; rewrite edge_adj Dx Lx.
Qed.

Lemma acyclic_children g x :
        acyclic g ->
        x \notin children g x.
Proof. by move/(acyclic_adj x); apply/contra/children_adj. Qed.

End AcyclicityLemmas.

(**********)
(* Cycles *)
(**********)

(* x is a cycle if x is reachable from x *)
(* by a path of size at least 1; *)
(* alternatively, if x is reachable from some successor of x *)

Definition cycles {V : link} {A} (g : partial_graph V A) : seq node :=
  nodes (kfilt g (fun x => x \in flatten (map (reach g) (adj g x)))).

Section CyclesLemmas.
Context {V : link} {A : Type}.
Implicit Type g : partial_graph V A.

Lemma cycles_undef : cycles (undef : partial_graph V A) = [::].
Proof. by rewrite /cycles pfundef dom_undef. Qed.

Lemma cycles0 : cycles (Unit : partial_graph V A) = [::].
Proof. by rewrite /cycles pfunit dom0. Qed.

Lemma cyclesD {g} : {subset cycles g <= nodes g}.
Proof. by move=>x; rewrite nodes_kfilt=>/andP []. Qed.

Lemma cyclesE g x :
        (x \in cycles g) =
        (x \in nodes g) && (x \in flatten (map (reach g) (adj g x))).
Proof. exact: nodes_kfilt. Qed.

(* characteristic properties of cycles *)
(* these are overlapping; use as varants by context *)

Lemma cyclesP g (x : node) :
        reflect (exists2 y : node, y \in adj g x & x \in reach g y)
                (x \in cycles g).
Proof.
rewrite cyclesE; apply/(iffP idP)=>[|[y Ay Rx]].
- by case/andP=>Dx /flatten_mapP [y Ay Ry]; exists y.
by rewrite (reachD Rx); apply/flatten_mapP; exists y.
Qed.

Lemma cyclesPD g (x : node) :
        reflect (x \in nodes g /\
                 exists2 y, y \in adj g x & x \in reach g y)
                (x \in cycles g).
Proof. by apply: (iffP idP)=>[/[dup]/cyclesD ->|[_]]/cyclesP. Qed.

Lemma cyclesPC g (x : node) :
         reflect (exists xs, cycle (edge g) (x :: xs))
                 (x \in cycles g).
Proof.
apply/(iffP (cyclesP _ _))=>/=.
- case=>y Ay /reachP [Dy][xs][P H]; exists (belast y xs).
  by rewrite H -lastI /= -H edge_adj Ay Dy P.
case; case=>[|y ys] /=.
- by rewrite edge_adj andbT=>/andP [Dx Ax]; exists x=>//; rewrite reach0.
rewrite rcons_path edge_adj -andbA=>/and4P [Dy Ay P X].
exists y=>//; apply/reachP; split=>//; exists (rcons ys x).
by rewrite rcons_path last_rcons P X.
Qed.

Lemma cyclesPCI g x xs :
        cycle (edge g) (x :: xs) ->
        x \in cycles g.
Proof. by move=>C; apply/cyclesPC; exists xs. Qed.

Lemma cyclesPCU g (x : node) :
        reflect (exists2 xs, cycle (edge g) (x :: xs) & uniq (x :: xs))
                (x \in cycles g).
Proof.
apply/(iffP (cyclesPC _ _))=>-[xs] /=; last by exists xs.
rewrite rcons_path=>/andP [/shortenP [xs' P U S] E].
by exists xs'=>//; rewrite rcons_path P E.
Qed.

(* this one seems most useful, so given short name *)
Lemma cyclesX g (x : node) :
        reflect (exists2 xs, cycle (edge g) xs & x \in xs)
                (x \in cycles g).
Proof.
apply/(iffP (cyclesPC _ _))=>-[xs].
- by exists (x :: xs)=>//; rewrite inE eqxx.
by move/[swap]=>X /(cycle_head_uniq X) [ys][]; exists ys.
Qed.

Lemma cyclesXI g (x : node) xs :
        x \in xs ->
        cycle (edge g) xs ->
        x \in cycles g.
Proof. by move=>X C; apply/cyclesX; exists xs. Qed.

Lemma cyclesXU g (x : node) :
        reflect (exists xs, [/\ cycle (edge g) xs, x \in xs & uniq xs])
                (x \in cycles g).
Proof.
apply/(iffP idP)=>[/cyclesPCU|][xs].
- by exists (x :: xs); rewrite inE eqxx.
by case=>*; apply/cyclesX; exists xs.
Qed.

(* subset properties of cycles *)

Lemma cycle_cycles_sub {g xs} :
        cycle (edge g) xs ->
        {subset xs <= cycles g}.
Proof. by move=>C x /cyclesXI/(_ C). Qed.

Lemma cyclesUn {g1 g2} :
        [pcm g1 <= g2] ->
        valid g2 ->
        {subset cycles g1 <= cycles g2}.
Proof.
case=>g -> W x /cyclesPD [Dx][y Ay Ry]; apply/cyclesP.
by exists y; rewrite ?adjUnL ?Dx ?reachUnL ?ifT.
Qed.

Lemma cyclesUnL {g1 g2} :
        valid (g1 \+ g2) ->
        {subset cycles g1 <= cycles (g1 \+ g2)}.
Proof. by apply: cyclesUn. Qed.

Lemma cyclesUnR {g1 g2} :
        valid (g1 \+ g2) ->
        {subset cycles g2 <= cycles (g1 \+ g2)}.
Proof. by apply: cyclesUn. Qed.

Lemma cyclesF {g} {x : node} :
         {subset cycles (free g x) <= cycles g}.
Proof.
case: (normalP g)=>[->|W]; first by rewrite free_undef.
by apply: cyclesUn (pleq_free _ _) _.
Qed.

Lemma cyclesNF {g} {x : node} :
         x \notin cycles g ->
         {subset cycles g <= cycles (free g x)}.
Proof.
move=>Nx y /cyclesX [xs C Y]; apply/cyclesX; exists xs=>//.
by apply/cycle_edge_free/C/(contra _ Nx)/cycle_cycles_sub.
Qed.

(* cycles monotonicity *)

Lemma cycles_kfilt_sub {g} p :
        {subset cycles (kfilt g p) <= cycles g}.
Proof.
case: (normalP g)=>[->|W y H]; first by rewrite pfundef.
by rewrite (kfiltC g p) cyclesUnL // -kfiltC.
Qed.

Lemma cycles_kfilt_mono {g} (p1 p2 : pred node) :
        {subset p1 <= p2} ->
        {subset cycles (kfilt g p1) <= cycles (kfilt g p2)}.
Proof.
case: (normalP g)=>[->|W S]; first by rewrite !pfundef.
rewrite (kfilt_predD g S); apply: cyclesUn=>//.
by rewrite valid_umfiltkUn // => z _ /= ->.
Qed.

Lemma cycles_kfilt_eq g (p1 p2 : pred node) :
        p1 =i p2 ->
        cycles (kfilt g p1) =i cycles (kfilt g p2).
Proof.
by move=>S y; apply/idP/idP; apply/cycles_kfilt_mono=>z; rewrite S.
Qed.

(* cycles and loops *)

Lemma loops_cycles_sub {g} : {subset loops g <= cycles g}.
Proof.
move=>x; rewrite loopsE=>/andP [Dx Ax]; apply/cyclesP.
by exists x=>//; rewrite reach0.
Qed.

(* the other direction holds in special case of preacylic graphs *)
Lemma preacyclic_sub {g} :
         preacyclic g ->
         {subset cycles g <= loops g}.
Proof.
move/preacyclicP=>/= H x /cyclesPCU [[|y xs]] // /[dup] C /=.
- by rewrite loops_cycleE.
rewrite edge_adj -andbA=>/and3P [Dy Ay _].
by rewrite (H x y) ?(cycle_nodes C,bireach_cycle C,inE,eqxx,orbT).
Qed.

Lemma cycles_loops_sub {g1 g2} :
        [pcm g1 <= g2] ->
        valid g2 ->
        {subset cycles g2 <= loops g2} ->
        {subset cycles g1 <= loops g1}.
Proof.
case=>g -> W H x /[dup]/(cyclesUnL W)/H; rewrite loopsUn //.
by case/orP=>// /(allP (disj_loopsR W)) /[swap]/cyclesD ->.
Qed.

Lemma cycles_loops_subL {g1 g2} :
        valid (g1 \+ g2) ->
        {subset cycles (g1 \+ g2) <= loops (g1 \+ g2)} ->
        {subset cycles g1 <= loops g1}.
Proof. by apply: cycles_loops_sub. Qed.

Lemma cycles_loops_subR {g1 g2} :
        valid (g1 \+ g2) ->
        {subset cycles (g1 \+ g2) <= loops (g1 \+ g2)} ->
        {subset cycles g2 <= loops g2}.
Proof. by apply: cycles_loops_sub. Qed.

Lemma bireach_cycles {g x y} :
        x != y ->
        y \in bireach g x ->
        y \in cycles g.
Proof.
move=>Nxy /(bireach_cycleP _ Nxy) [xs Y C].
by apply/cyclesXI/C; rewrite inE Y orbT.
Qed.

End CyclesLemmas.


(**********)
(* Closed *)
(**********)

(* predicate testing that no edges are dangling *)

Definition closed {V : link} {A} (g : partial_graph V A) :=
  all [mem nodes0 g] (sinks g).

Section Closed.
Context {V : link} {A : Type}.
Implicit Type g : partial_graph V A.

Lemma closedP g : reflect {subset sinks g <= nodes0 g} (closed g).
Proof. exact: allP. Qed.

Lemma closed_undef : closed (undef : partial_graph V A).
Proof. by []. Qed.

Lemma closed_unit : closed (Unit : partial_graph V A).
Proof. by []. Qed.

Lemma closed_erase g : closed (erase g) = closed g.
Proof. by rewrite /closed sinks_erase nodes_erase. Qed.

End Closed.

Section ClosedLemmas.
Context {V : link} {A : Type}.
Implicit Type g : partial_graph V A.

Lemma In_closed x v a g :
        (x, (v, a)) \In g ->
        reflect ({subset links a <= nodes0 g} /\
                 {subset sinks (free g x) <= nodes0 g})
                (closed g).
Proof.
move=>H; move: (In_eta H) (In_valid H)=>E W; rewrite E in W.
case: closedP=>X; constructor.
- by split=>/= z Z; move: (X z); rewrite {1}E sinksPtUn
        ?(validX W) //= mem_cat Z ?orbT; apply.
case=>H1 H2; apply: X=>z.
rewrite {1}E sinksPtUn ?(validX W) //= mem_cat.
by case/orP=>[/H1|/H2].
Qed.

Lemma closed_links x v a g :
        (x, (v, a)) \In g ->
        closed g ->
        {subset links a <= nodes0 g}.
Proof. by move=>H /(In_closed H) []. Qed.

Lemma closed_sinks x g :
        x \in nodes g ->
        closed g ->
        {subset sinks (free g x) <= nodes0 g}.
Proof. by case/In_domX=>-[a v] H /(In_closed H) []. Qed.

Lemma In_closedPtUn x v a g :
        x \in nodes g ->
        closed g ->
        reflect {subset links a <= nodes0 g}
                (closed (pts x (v, a) \+ free g x)).
Proof.
move=>D C; case X: (closed _); constructor; case/In_domX: D=>-[v' a'] H;
move: (In_eta H) (In_valid H)=>E W; rewrite E in W;
have K : (x, (v, a)) \In pts x (v, a) \+ free g x
  by apply/InPtUnL/(validX W).
- rewrite E -(domPtUnE2 x (v, a)); apply: closed_links K X.
move/negP: X=>X Y; apply: X; apply/(In_closed K);
rewrite -(domPtUnE2 x (v', a')) -E freePtUn ?(validX W) //.
by split=>//; apply: closed_sinks (In_dom H) C.
Qed.

Lemma closedUn g1 g2 :
        closed g1 ->
        closed g2 ->
        closed (g1 \+ g2).
Proof.
case: (normalP (g1 \+ g2))=>[->|W]; first by rewrite closed_undef.
move/closedP=>S1 /closedP S2; apply/closedP=>/= x.
rewrite sinksUnE // inE domUnE //= => /orP [/S1|/S2];
by rewrite inE; case/orP=>-> //; rewrite !orbT.
Qed.

Lemma closed_ext g1 g2 :
        closed g1 ->
        disjoint (sinks g1) (filter [predC nodes g1] (nodes g2)).
Proof.
move/closedP=>S; apply/disj_filt_subL=>x /S; rewrite !inE negb_and negbK.
by case/orP=>[/eqP|] -> //; rewrite !mem_dom0.
Qed.

(* if g1 is closed, there's no edges crossing into g2 *)
Lemma closed_edgeE g1 g2 x y :
        valid (g1 \+ g2) ->
        closed g1 ->
        x \in nodes g1 ->
        edge (g1 \+ g2) x y = edge g1 x y.
Proof.
move=>W /closedP S Dx; rewrite !edge_adj adjUnL // Dx domUnE //.
apply/andb_id2r=>/adj_sinks_sub/S; rewrite inE orbC.
by case: (y \in nodes g1)=>//= /eqP ->; rewrite cond_dom.
Qed.

Lemma closed_edge g1 g2 x y :
        closed g1 ->
        x \in nodes g1 ->
        y \in nodes g2 ->
        ~ (edge (g1 \+ g2) x y).
Proof.
case: (normalP (g1 \+ g2))=>[->|W C]; first by rewrite edge_undef.
by move/(closed_edgeE _ W C)=>-> Dy /edgeD [_] /(dom_inNLX W).
Qed.

Lemma closed_pathL g1 g2 x xs :
        closed g1 ->
        x \in nodes g1 ->
        path (edge (g1 \+ g2)) x xs ->
        path (edge g1) x xs.
Proof.
case: (normalP (g1 \+ g2))=>[->|W]; first by case: xs.
elim: xs x=>[|y xs IH] //= x C Dx /andP [].
by rewrite closed_edgeE // => E P; rewrite E /= IH // (edgeD E).
Qed.

Lemma closed_pathR g1 g2 x xs :
        closed g2 ->
        x \in nodes g2 ->
        path (edge (g1 \+ g2)) x xs ->
        path (edge g2) x xs.
Proof. by rewrite joinC; apply: closed_pathL. Qed.

Lemma reach_closedUn g1 g2 x :
        [pcm g1 <= g2] ->
        closed g1 ->
        x \in nodes g1 ->
        {subset reach g2 x <= reach g1 x}.
Proof.
case=>g ->; case: (normalP (g1 \+ g))=>[->|W] C D y.
- by rewrite reach_undef.
case/reachP=>_ [xs][P L]; apply/reachP; split=>//=.
by exists xs; split=>//; apply: closed_pathL P.
Qed.

Lemma reach_closedL g1 g2 x :
        closed g1 ->
        x \in nodes g1 ->
        {subset reach (g1 \+ g2) x <= reach g1 x}.
Proof. by apply: reach_closedUn. Qed.

Lemma reach_closedR g1 g2 x :
        closed g2 ->
        x \in nodes g2 ->
        {subset reach (g1 \+ g2) x <= reach g2 x}.
Proof. by apply: reach_closedUn. Qed.

Lemma bireach_closedL g1 g2 x y  :
        closed g1 ->
        x \in nodes g1 ->
        y \in nodes g1 ->
        x \in bireach (g1 \+ g2) y ->
        x \in bireach g1 y.
Proof.
case: (normalP (g1 \+ g2))=>[->|W C Dx Dy].
- by rewrite /bireach mem_filter reach_undef.
by rewrite !mem_filter=>/andP [/(reach_closedL C Dx)] -> /(reach_closedL C Dy).
Qed.

Lemma bireach_closedR g1 g2 x y  :
        closed g2 ->
        x \in nodes g2 ->
        y \in nodes g2 ->
        x \in bireach (g1 \+ g2) y ->
        x \in bireach g2 y.
Proof. by rewrite joinC; apply: bireach_closedL. Qed.

Lemma closed_preacyclicUn g1 g2 :
        closed g1 ->
        closed g2 ->
        preacyclic g1 ->
        preacyclic g2 ->
        preacyclic (g1 \+ g2).
Proof.
case: (normalP (g1 \+ g2))=>[->|W C1 C2].
- by rewrite preacyclic_undef.
move/preacyclicP=>P1 /preacyclicP P2; apply/preacyclicP=>x y.
rewrite !domUnE //; case/orP=>Dx /orP [] Dy.
- by move/(bireach_closedL C1 Dy Dx)/(P1 _ _ Dx Dy).
- rewrite mem_filter=>/andP [_] /(reach_closedL C1 Dx).
  by case/reachD=>_ /(dom_inNRX W Dy).
- rewrite mem_filter=>/andP [/(reach_closedL C1 Dy)].
  by case/reachD=>_ /(dom_inNRX W Dx).
by move/(bireach_closedR C2 Dy Dx)/(P2 _ _ Dx Dy).
Qed.

Lemma closed_freeN g x :
        closed g ->
        x \notin sinks (free g x) ->
        closed (free g x).
Proof.
move/closedP=>C NSx; apply/closedP=>y.
case: (y =P x)=>[->|/eqP N /sinks_free_sub/C]; first by rewrite (negbTE NSx).
by rewrite !inE domF N.
Qed.

End ClosedLemmas.

Arguments In_closedPtUn {V A x v a g}.

(* reach and closed *)

Section ReachClosed.
Context {V : link} {A : Type}.
Implicit Type g : partial_graph V A.

Lemma closed_reach g x :
        closed g ->
        closed (kfilt g [in reach g x]).
Proof.
move/closedP=>H; apply/closedP=>y /sinksPA [z].
rewrite inE nodes_kfilt adj_kfilt; case: ifP=>// Rz Ay.
have /H : y \in sinks g by apply/sinksPA; exists z.
rewrite inE; case/orP=>[->//|Dy]; rewrite Dy /=.
by rewrite (reach_edgeI Rz) ?orbT // edge_adj Dy Ay.
Qed.

Lemma closed_reachUn g1 g2 x :
        closed (g1 \+ g2) ->
        nodes g1 =i reach (g1 \+ g2) x ->
        closed g1.
Proof.
case: (normalP (g1 \+ g2))=>[-> _|W C N].
- rewrite reach_undef=>N.
  by apply/closedP=>y /sinksP [z]; rewrite N.
have E : g1 = kfilt (g1 \+ g2) [in reach (g1 \+ g2) x].
- by rewrite -(kfilt_eq _ N) kfiltUn_nodes.
by rewrite E closed_reach.
Qed.

(* the next two lemmas aren't about closed *)
(* but are always used together with closed_reachUn *)

Lemma nodes_reachUn g1 g2 x :
        nodes g1 =i reach (g1 \+ g2) x ->
        nodes g1 =i reach g1 x.
Proof.
case: (normalP (g1 \+ g2))=>[->|W N].
- rewrite reach_undef=>N y.
  by apply/idP/reachP=>[|[]]; rewrite N.
have E : g1 = kfilt (g1 \+ g2) [in reach (g1 \+ g2) x].
- by rewrite -(kfilt_eq _ N) kfiltUn_nodes.
by move=>y; rewrite {2}E reach_reach -N.
Qed.

Lemma nodes_reachUnL g1 g2 x :
        nodes g1 =i reach (g1 \+ g2) x ->
        x \in nodes (g1 \+ g2) ->
        x \in nodes g1.
Proof. by move=>N Dx; rewrite N reach0. Qed.

(* common usage *)
Lemma closed_reachUnX g1 g2 x :
        closed (g1 \+ g2) ->
        x \in nodes (g1 \+ g2) ->
        nodes g1 =i reach (g1 \+ g2) x ->
        [/\ closed g1, x \in nodes g1 &
            nodes g1 =i reach g1 x].
Proof.
move=>C Dx N; split.
- by apply: closed_reachUn C N.
- by apply: nodes_reachUnL N Dx.
by apply: nodes_reachUn N.
Qed.

End ReachClosed.

(**********************)
(* Dangls and dangls0 *)
(**********************)

(* sinks of dangling edges in g *)
(* two different variants : *)
(* dangls  = sings g \ nodes0 g explicitly excludes null *)
(* dangls0 = sinks g \ nodes g  may include null if sinks includes null *)

Definition dangls {V : link} A (g : partial_graph V A) :=
  filter [predC nodes0 g] (sinks g).

Definition dangls0 {V : link} {A} (g : partial_graph V A) :=
  filter [predC nodes g] (sinks g).

Section DanglsLemmas.
Context {V : link} {A : Type}.
Implicit Types g : partial_graph V A.

Lemma dangls0E g : dangls g = filter (predC1 null) (dangls0 g).
Proof. by rewrite -filter_predI; apply: eq_filter=>x; rewrite inE negb_or. Qed.

Lemma dangls_mem g x :
        (x \in dangls g) = (x \notin nodes0 g) && (x \in sinks g).
Proof. by rewrite mem_filter. Qed.

Lemma dangls0_mem g x :
        (x \in dangls0 g) = (x \notin nodes g) && (x \in sinks g).
Proof. by rewrite mem_filter. Qed.

Lemma dangls_dangls0_sub {g} : {subset dangls g <= dangls0 g}.
Proof. by move=>x; rewrite !mem_filter /= inE negb_or -andbA=>/andP []. Qed.

Lemma dangls0_nodesD {g} : disjoint (dangls0 g) (nodes g).
Proof. by apply/allP=>x D; rewrite mem_filter /= D. Qed.

Lemma dangls_nodes0D {g} : disjoint (dangls g) (nodes0 g).
Proof. by apply/allP=>x D; rewrite mem_filter /= D. Qed.

Lemma dangls0_loops_disj {g} : disjoint (dangls0 g) (loops g).
Proof. by apply/disjoint_subL/dangls0_nodesD/omf_subdom. Qed.

Lemma danglsUn g1 g2 x :
        valid (g1 \+ g2) ->
        (x \in dangls (g1 \+ g2)) =
        (x \in filter [predC nodes g2] (dangls g1)) ||
        (x \in filter [predC nodes g1] (dangls g2)).
Proof.
move=>W; rewrite /dangls -!filter_predI !mem_filter /=.
rewrite [in RHS]inE negb_or andbCA andbA -negb_or (andbC (x \notin nodes0 g2)).
by rewrite -andb_orr -negb_or -sinksUnE // -nodesUn0R.
Qed.

Lemma dangls0Un g1 g2 x :
        valid (g1 \+ g2) ->
        (x \in dangls0 (g1 \+ g2)) =
        (x \in filter [predC nodes g2] (dangls0 g1)) ||
        (x \in filter [predC nodes g1] (dangls0 g2)).
Proof.
move=>W; rewrite /dangls0 -!filter_predI !mem_filter /=.
rewrite (andbC (x \notin nodes g2)).
by rewrite -andb_orr -negb_or -sinksUnE // -domUnE.
Qed.

Lemma closed_danglsE g : closed g = nilp (dangls g).
Proof. by rewrite filter_nilp; apply/allP/hasPn=>H x /H; rewrite negbK. Qed.

Lemma closed_dangls0E g : closed g = all (pred1 null) (dangls0 g).
Proof. by rewrite closed_danglsE dangls0E filter_nilp has_predC negbK. Qed.

Lemma edge_broken g1 g2 x y :
        edge (g1 \+ g2) x y ->
        ~~ edge g1 x y ->
        x \in nodes g1 ->
        [/\ y \in nodes g2, y \in adj g1 x & y \in dangls0 g1].
Proof.
case: (normalP (g1 \+ g2))=>[->|W /[dup] E + N Dx]; first by rewrite edge_undef.
rewrite edge_adj (edgeD E) /= adjUnL // Dx => Ay1.
have Dy : y \notin nodes g1 by apply: contra N; move/adj_edge; apply.
split=>//; last by rewrite mem_filter /= Dy; apply/sinksPA; exists x.
by case: (edgeD E)=>_; rewrite domUnE // (negbTE Dy).
Qed.

Lemma path_broken g1 g2 x xs :
        x \in nodes g1 ->
        path (edge (g1 \+ g2)) x xs ->
        path (edge g1) x xs \/
        exists y z, [/\ y \in nodes g1, y \in x :: xs,
                        z \in nodes g2, z \in xs,
                        z \in adj g1 y & z \in dangls0 g1].
Proof.
case: xs=>[|y ys] // Dx P; first by left.
have [] := boolP (path (edge g1) x (y::ys)); first by left.
case/(pathPn null)=>i [/[dup] H1 /(pathP null P i) H4 H2 H3]; right.
case: i H1 H2 H3 H4=>[|i] H1 H2 H3 H4 {P}.
- by exists x, y; rewrite Dx !inE !eqxx; case: (edge_broken H4 H2 Dx).
move/(_ i (ltnSn _)): H3=>/edgeD [_ D2].
case: (edge_broken H4 H2 D2)=>/= Dn2 An1 Dngl.
exists (nth null [:: x, y & ys] i.+1), (nth null (y :: ys) i.+1).
by split=>//; apply: mem_nth=>//; apply: ltn_trans H1 _.
Qed.

Lemma cycle_broken g1 g2 x xs :
        x \in nodes g1 ->
        cycle (edge (g1 \+ g2)) (x :: xs) ->
        cycle (edge g1) (x :: xs) \/
          exists y, [/\ y \in xs, y \in nodes g2 & y \in dangls0 g1].
Proof.
case: (normalP (g1 \+ g2))=>[->|W Dx] /=.
- by rewrite rcons_path edge_undef andbF.
case/(path_broken Dx)=>[P|[y][z][_ _ Dz2 Rz _ Dlz1]]; first by left.
rewrite mem_rcons inE in Rz.
case: eqP Rz Dx Dz2=>[-> _ Dx /(dom_inNLX W Dx)//|/eqP N X Dx Dz2].
by right; exists z.
Qed.

End DanglsLemmas.

(**********)
(* Summit *)
(**********)

(* summit g x = locus of nodes where a path from x *)
(* exits the graph g, or loops back on itself *)

(* n - fuel to run; ghost arg to be instantiated to size (nodes g) *)
Fixpoint summit' {V : link} {A} (n : nat) (g : partial_graph V A) x :=
  if n is n'.+1 then
    if x \in nodes g then
      \big[cat/[::]]_(y <- adj g x) summit' n' (free g x) y
    else [:: x]
  else [:: x].

Definition summit {V : link} {A} (g : partial_graph V A) :=
  @summit' V A (size (nodes g)) g.

Section SummitLemmas.
Context {V : link} {A : Type}.
Implicit Type g : partial_graph V A.

(* characteristic property of summit *)
Lemma summitP g (x y : node) :
        y \in summit g x <->
        exists xs, [/\ path (edge g) x xs, uniq (x :: xs),
          if x \in nodes g then y \in adj g (last x xs) else y == x &
          y \notin nodes g \/ y \in x :: xs].
Proof.
rewrite /summit; move: {-1}(size (nodes g)) (erefl (size (nodes g)))=>size.
elim: size g y x=>[|n IH] g /= y x S.
- rewrite inE (size0nil S); split=>[|[xs][P] /andP [X U]] /eqP ->{y} //.
  by exists [::]; split=>//=; left.
case: ifP=>Dx; last first.
- rewrite inE; split=>[|[xs][P] /andP [X U]] /eqP ->{y} //.
  by exists [::]; rewrite Dx; split=>//=; left.
have {}S : size (nodes (free g x)) = n by rewrite size_domF // S.
split=>[|[xs][P] /andP [N U] Ay H].
- case/big_cat_memE=>z Az /IH [] //= xs [P] /andP [N U].
  rewrite !domF adjF inE negb_and negbK => H.
  case: (z =P x) H Az P N U=>[->{z}|/eqP Nz] /=.
  - move/eqP=>->{y}; case: xs=>[|z zs] /=.
    - by exists [::]; split=>//; rewrite inE; right.
    by rewrite edgeFE eqxx andbF.
  case: ifPn=>Dz; last by move/eqP=>->{y}; exists [::]; split=>//; left.
  case: ifPn=>// Lx Ay Az P Nxs U H; exists (z :: xs); split=>//=; rewrite ?inE.
  - by rewrite edge_adj Dz Az (sub_path free_edge_sub P).
  - rewrite negb_or eq_sym Nz Nxs U !andbT /=.
    by apply/negP=>/(path_nodes P); rewrite domF eqxx.
  by case: H=>/orP [] ->; [right|left|right|right]; rewrite ?orbT.
apply/big_cat_memE; case: xs H P N U Ay=>[|z zs] /=; rewrite !inE ?negb_or=>H.
- exists y=>//; apply/IH=>//; exists [::].
  split=>//; last by rewrite inE; right.
  by rewrite domF; case: H=>[/negbTE|] -> //=; rewrite andbF.
case/andP=>E P /andP [Nxz Nxzs] /andP [Nzzs Uz] Ay.
exists z; first by apply: edgeA.
apply/IH=>//=; exists zs; split.
- by rewrite path_edge_free // inE negb_or Nxz Nxzs.
- by rewrite Nzzs Uz.
- rewrite domF eq_sym Nxz (edgeD E) adjF /=.
  by case: (x =P last z zs) Nxz Nxzs=>// /last_mem/orP [] ->.
rewrite domF negb_and negbK inE.
by case: H=>[|/or3P []] ->; [left|left|right|right]; rewrite ?orbT.
Qed.

Lemma summit_notin g x :
        x \notin nodes g ->
        summit g x = [:: x].
Proof. by rewrite /summit; case: (size (nodes g))=>//= n /negbTE ->. Qed.

Lemma summit_undef x :
        summit (undef : partial_graph V A) x = [:: x].
Proof. by rewrite /summit dom_undef. Qed.

Lemma summit_unit x :
        summit (Unit : partial_graph V A) x = [:: x].
Proof. by rewrite /summit dom0. Qed.

Lemma summitPt2 v x xs y :
        summit (pts x (v, xs) : partial_graph V A) y =
        if (x != 0) && (y == x) then links xs else [:: y].
Proof.
rewrite /summit domPtK; case: ifPn=>//= N.
rewrite domPtK adjPt2 N inE; case: eqP=>// _.
by elim: (links xs)=>[|z zs IH]; rewrite ?big_nil ?big_cons ?IH.
Qed.

Lemma summitPt v x xs :
        summit (pts x (v, xs) : partial_graph V A) x =
        if x != 0 then links xs else [:: x].
Proof. by rewrite summitPt2 eqxx andbT. Qed.

Lemma summit_dangl g x y :
        y \in adj g x ->
        y \notin nodes g ->
        y \in summit g x.
Proof.
by move=>Ay Dy; apply/summitP; exists [::]; rewrite (adjD Ay); split=>//; left.
Qed.

Lemma summit_cycles g x :
        x \in cycles g ->
        x \in summit g x.
Proof.
case/cyclesPCU=>xs /=; rewrite rcons_path=>/andP [P E] U.
apply/summitP; exists xs; rewrite (edgeD E) (edgeA E) inE eqxx.
by split=>//; right.
Qed.

Lemma summit_leaves g x :
        x \in leaves g ->
        {subset summit g x <= [:: null]}.
Proof.
case/leavesP=>Dx /= H y /summitP [xs][]; rewrite Dx !inE.
case: xs=>[_ _ /H|z zs] //= /andP []/[dup]/edgeA/H /eqP -> /edgeD [_].
by rewrite mem_dom0.
Qed.

End SummitLemmas.

(***********)
(* Summits *)
(***********)

(* collecting the summits of all the nodes in g *)

Definition summits {V : link} {A} (g : partial_graph V A) : seq node :=
  flatten (map (summit g) (nodes g)).

Section SummitsLemmas.
Context {V : link} {A : Type}.
Implicit Type g : partial_graph V A.

Lemma summit_summits_sub g x :
        x \in nodes g ->
        {subset summit g x <= summits g}.
Proof. by move=>Dx y Sy; apply/flatten_mapP; exists x. Qed.

Lemma summits_undef :
        summits (undef : partial_graph V A) = [::].
Proof. by rewrite /summits dom_undef. Qed.

Lemma summits_unit :
        summits (Unit : partial_graph V A) = [::].
Proof. by rewrite /summits dom0. Qed.

Lemma summitsPt v x xs :
        summits (pts x (v, xs) : partial_graph V A) =
        if x != 0 then links xs else [::].
Proof.
by rewrite /summits domPtK; case: ifP=>//= N; rewrite cats0 summitPt N.
Qed.

Lemma cycles_summits_sub {g} : {subset cycles g <= summits g}.
Proof.
move=>x /cyclesPD [Dx][y Ay] /reachX [Dy][xs][P L U].
apply/flatten_mapP; exists x=>//; apply/summitP; exists (belast y xs).
case: xs P U L Ay=>[_ _ -> /= Ay|z zs].
- by rewrite Dy inE eqxx; split=>//; right.
rewrite {1}lastI rcons_path=>/andP [P1 /edgeA P2] U L Ay.
rewrite lastI -L rcons_uniq in U; split=>//=.
- by rewrite adj_edge.
- by rewrite Dx L.
by rewrite inE eqxx; right.
Qed.

Lemma dangls0_summits_sub {g} : {subset dangls0 g <= summits g}.
Proof.
move=>x; rewrite mem_filter inE=>/andP [Dnx /sinksP [y Dy Ay]].
apply/flatten_mapP; exists y=>//; apply/summitP; exists [::].
by rewrite Dy; split=>//; left.
Qed.

(* characteristic property: summits = cycles + dangls0 *)

Lemma summits_cycles_dangls0E g x :
        (x \in summits g) =
        (x \in cycles g) || (x \in dangls0 g).
Proof.
apply/idP/orP; last by case=>[/cycles_summits_sub|/dangls0_summits_sub].
case/flatten_mapP=>y Dy /summitP [ys][P _]; rewrite Dy inE=>L.
have S : {subset y :: ys <= nodes g} by apply/subset_consLI/(path_nodes P).
case=>X; [right|left; apply/cyclesP].
- rewrite mem_filter /= X; apply/sinksP.
  by exists (last y ys)=>//; apply/S/mem_last.
have El : edge g (last y ys) x by apply/adj_edge/L/S.
case/orP: X P L El=>[/eqP ->|X] P L El.
- exists (head y ys); first by case: ys P L {S El}=>// z zs /andP [/edgeA].
  apply/reachP; split; first by apply/S/head_mem.
  exists (behead (rcons ys y)); split; last first.
  - by case: ys {P L S El}=>//= z zs; rewrite last_rcons.
  suff : path (edge g) y (rcons ys y) by rewrite headI=>/andP [].
  by rewrite rcons_path P.
case/splitPr: {S} X P El L=>p1 p2; rewrite cat_path last_cat.
case/andP=>_ /[dup] Px /= /andP [_ P2] El L; exists (head x p2).
- by case: p2 P2 L {Px El}=>//= z zs /andP [/edgeA].
apply/reachP; split; first by apply/(path_nodes Px)/(head_mem x p2).
exists (behead (rcons p2 x)).
split; last by case: p2 {Px P2 El L}=>//= z xs; rewrite last_rcons.
suff : path (edge g) x (rcons p2 x) by rewrite headI=>/andP [].
by rewrite rcons_path P2 El.
Qed.

Lemma loops_summits_sub {g} : {subset loops g <= summits g}.
Proof. by move=>x /loops_cycles_sub/cycles_summits_sub. Qed.

Lemma in_nodes_summitsE g x :
        x \in nodes g ->
        (x \in summits g) = (x \in cycles g).
Proof.
by rewrite summits_cycles_dangls0E orbC=>/(allP dangls0_nodesD)/negbTE ->.
Qed.

Lemma notin_nodes_summitsE g x :
        x \notin nodes g ->
        (x \in summits g) = (x \in dangls0 g).
Proof.
by rewrite summits_cycles_dangls0E=>/negP Nx; apply/orb_idl=>/cyclesD.
Qed.

Lemma closed_summits_sub g :
        closed g ->
        {subset summits g <= null :: cycles g}.
Proof.
rewrite closed_dangls0E=>D x; rewrite summits_cycles_dangls0E inE.
by case/orP=>[|/(allP D)/=] -> //; rewrite orbT.
Qed.

Lemma summits_closed0 g :
        reflect {subset summits g <= nodes0 g}
                (closed g).
Proof.
apply: (iffP idP)=>[|S].
- move/closed_summits_sub=>S x /S; rewrite !inE.
  by case/orP=>[->//|/cyclesD ->]; rewrite orbT.
apply/closedP=>x /sinksP [y Ny Ay]; apply/wlog_neg=>Dx.
rewrite S ?dangls0_summits_sub // dangls0_mem (adj_sinks_sub Ay) andbT.
by apply: contra Dx=>Dx; rewrite inE Dx orbT.
Qed.

Lemma summitsUn {g1 g2 x} :
         valid (g1 \+ g2) ->
         preacyclic (g1 \+ g2) ->
         (x \in summits (g1 \+ g2)) =
         (x \in filter [predC nodes g2] (summits g1)) ||
         (x \in filter [predC nodes g1] (summits g2)).
Proof.
move=>W /preacyclic_sub P; rewrite summits_cycles_dangls0E.
rewrite (subset_eq P loops_cycles_sub) loopsUn // dangls0Un //= -!orbA.
rewrite (orbCA (x \in loops g2)) -(filter_disjC (disj_loopsL W)).
rewrite -(filter_disjC (disj_loopsR W)) orbA -!mem_cat -!filter_cat 2!mem_cat.
rewrite !mem_filter /= !mem_cat.
rewrite (subset_eq loops_cycles_sub (cycles_loops_subL W P)).
rewrite (subset_eq loops_cycles_sub (cycles_loops_subR W P)).
by rewrite !summits_cycles_dangls0E.
Qed.

(* node cannot be a cycle in two disjoint graphs *)
(* if a summit is not a cycle it must be dangl *)

Lemma summitsEq_subL g1 g2 :
        valid (g1 \+ g2) ->
        summits g1 =i summits g2 ->
        {subset cycles g1 <= dangls0 g2}.
Proof.
move=>W C x /[dup] /cyclesD Dx /cycles_summits_sub; rewrite C.
by move: (dom_inNL W  Dx)=>Dnx Cx; rewrite -notin_nodes_summitsE.
Qed.

Lemma summitsEq_subR g1 g2 :
        valid (g1 \+ g2) ->
        summits g1 =i summits g2 ->
        {subset cycles g2 <= dangls0 g1}.
Proof. by rewrite joinC=>W C; apply: summitsEq_subL. Qed.

End SummitsLemmas.


(****************)
(****************)
(* Unary graphs *)
(****************)
(****************)

(* unary graphs have singleton list for linkage *)

Definition single_links (x : node) := [:: x].
Definition single_mk (s : seq node) :=
  if s is [:: a] then Some a else None.
Arguments single_links x /.
Arguments single_mk s /.
Lemma single_is_link : link_axiom single_links single_mk.
Proof. by split; case=>// a []. Qed.
HB.instance Definition _ := isLink.Build node single_is_link.
Abbreviation unary_graph A := (partial_graph node A).
Notation "x &1-> v" := (ptsT (unary_graph _) x v) (at level 30).

(* graphs with fixed arity have special names for children *)
(* for unary graphs, we call the child nxt *)

(* nxt is immediate node after x in graph g *)
(* if x \notin g, the default is to return x *)
(* it's possible to make other defaults (e.g., null) *)
(* but other choices complicate somewhat *)
(* the characteristic property given below *)

Definition nxt A (g : unary_graph A) (x : node) : node :=
  head x (adj g x).

Section UnaryLemmas.
Context {A : Type}.
Implicit Types (g : unary_graph A) (x y z : node) (v : A).

Lemma nxt_notin g x :
        x \notin nodes g ->
        nxt g x = x.
Proof. by rewrite /nxt=>/adjND ->. Qed.

Lemma adj_nxt g x :
        x \in nodes g ->
        adj g x = [:: nxt g x].
Proof. by rewrite /nxt=>/In_graphX [v][xs][_] ->. Qed.

Lemma inj_edge g x y1 y2 :
        edge g x y1 ->
        edge g x y2 ->
        y1 = y2.
Proof.
move/[dup]/edgeD=>[Dx _]; rewrite !edge_adj adj_nxt // !inE.
by case/andP=>_ /eqP <- /andP [_] /eqP.
Qed.

Lemma In_nxt g x v y :
        (x, (v, y)) \In g ->
        y = nxt g x.
Proof. by rewrite /nxt=>/In_graph ->. Qed.

(* opposite direction *)
Lemma In_graph1X  g x :
        x \in nodes g ->
        exists v y, (x, (v, y)) \In g /\ nxt g x = y.
Proof. move/In_domX=>[[v] y] G; exists v, y; split=>//; apply/esym/(In_nxt G). Qed.

Lemma nxt_in g x :
        nxt g x \in nodes g ->
        x \in nodes g.
Proof. by apply: contraTT=>/[dup]/nxt_notin ->. Qed.

Lemma nxt_pts v x y :
        x != 0 ->
        nxt (pts x (v, y) : unary_graph A) x = y.
Proof. by move=>N; rewrite /nxt /adj //findPt ifT. Qed.

Lemma nxt_ptsUn g x y v :
        valid (pts x (v, y) \+ g) ->
        nxt (pts x (v, y) \+ g) x = y.
Proof. by move=>W; apply/esym; move: (In_nxt (InPtUnL W)). Qed.

Lemma leaves1E g x :
        (x \in leaves g) =
        (x \in nodes g) && (nxt g x == null).
Proof. by rewrite leavesE; apply/andb_id2l=>?; rewrite adj_nxt ?all_seq1. Qed.

Lemma nxt_notleaves g x :
        x \in nodes g ->
        (x \notin leaves g) = (nxt g x != null).
Proof. by rewrite leaves1E negb_and=>->. Qed.

Lemma nxt_in_sinks g x:
        x \in nodes g ->
        nxt g x \in sinks g.
Proof. by move=>Dx; apply/sinksPA; exists x; rewrite adj_nxt ?inE. Qed.

Lemma nxt_closed g x :
        x \in nodes g ->
        closed g ->
        nxt g x \in nodes0 g.
Proof. by move/nxt_in_sinks=>X /closedP; apply. Qed.

Lemma nxt_leaves_closed g x :
        x \in nodes g ->
        x \notin leaves g ->
        closed g ->
        nxt g x \in nodes g.
Proof.
move=>Dx; rewrite nxt_notleaves // => N /(nxt_closed Dx).
by rewrite inE (negbTE N).
Qed.

Lemma loops1E g x :
        (x \in loops g) =
        (x \in nodes (kfilt g (fun x => x == nxt g x))).
Proof.
rewrite !nodes_kfilt -!topredE /=; apply/andP/andP; case=>Dx;
by rewrite (adj_nxt Dx) inE.
Qed.

Lemma cycles1E g x :
        (x \in cycles g) =
        (x \in reach g (nxt g x)).
Proof.
rewrite cyclesE; apply/andP; case: ifP=>C; last first.
- by case=>Dx; rewrite adj_nxt //= cats0 C.
by case/reachP: (C)=>/[dup]/nxt_in D N _; rewrite adj_nxt //= cats0.
Qed.

Lemma nxt_free_notin g x y :
        x != y ->
        nxt (free g y) x = nxt g x.
Proof. by move=>N; rewrite /nxt adjF eq_sym (negbTE N). Qed.

Lemma cycle1_nxt g x xs :
        cycle (edge g) xs ->
        x \in xs ->
        nxt g x \in xs.
Proof.
case: xs=>//= y ys /[dup]/path_nodes S P /[dup] X; rewrite -!mem_rcons=>/S Dx.
case/(path_next X): P=>z [Rz]; rewrite edge_adj adj_nxt // inE.
by case/andP=>Dz /eqP <-.
Qed.

Lemma cycle1_path_sub g xs y ys :
        cycle (edge g) xs ->
        y \in xs ->
        path (edge g) y ys ->
        {subset ys <= xs}.
Proof.
case: xs=>// x xs C; elim: ys y=>//= y' ys IH y /[dup] Y.
rewrite -mem_rcons=>/[dup] Ry /(path_nodes C) Dy /andP [].
rewrite edge_adj adj_nxt // inE => /andP [Dy'] /eqP N'.
move/(cycle1_nxt C): Y; rewrite -N' => Ngy Pys.
by apply: subset_consLI Ngy (IH y' Ngy Pys).
Qed.

Lemma cycle1_reach_sub g x xs :
        cycle (edge g) xs ->
        x \in xs ->
        {subset reach g x <= xs}.
Proof.
case: xs=>// y ys C In z; case: (x =P z)=>[<-|/eqP Neq] //.
case/reachP=>Dx [xs'][P L]; apply: (cycle1_path_sub C In P).
by move: (mem_last x xs'); rewrite -L inE eq_sym (negbTE Neq).
Qed.

Lemma reach_cycles1_sub g x :
        x \in cycles g ->
        {subset reach g x <= cycles g}.
Proof.
case/cyclesX=>xs C /(cycle1_reach_sub C)=>S y /S Y.
by apply: cyclesXI Y C.
Qed.

Lemma cycles1_nxt g x :
        x \in cycles g ->
        nxt g x \in cycles g.
Proof. by case/cyclesX=>xs C /(cycle1_nxt C)/(cycle_cycles_sub C). Qed.

Lemma nxt_notin_cycles g x :
        nxt g x \notin nodes g ->
        x \notin cycles g.
Proof. by apply: contra=>/cycles1_nxt/cyclesD. Qed.

Lemma loops1_reach g x :
        x \in loops g ->
        reach g x =i [:: x].
Proof.
rewrite loops1E nodes_kfilt=>/andP [Dx /eqP Nxt] y.
rewrite reachEAX Dx !inE adj_nxt //= big_cons big_nil -Nxt.
by rewrite reachDN ?orbF // domF eqxx.
Qed.

Lemma loops1_reachE g x :
        x \in loops g ->
        reach g x = [:: x].
Proof. by move=>L; apply/undup_uniq_eq1/loops1_reach/L/uniq_reach. Qed.

Lemma In_loops1P g x :
        reflect (exists v, (x, (v, x)) \In g)
                (x \in loops g).
Proof.
apply: (iffP (In_loopsP _ _))=>[[v][a][/[swap]]|[v H]].
- by rewrite inE=>/eqP ->; exists v.
by exists v, x; rewrite inE.
Qed.

Lemma In_loops1 g x v :
        (x, (v, x)) \In g ->
        x \in loops g.
Proof. by move=>H; apply/In_loops1P; exists v. Qed.

Lemma In_loops1N g x y v :
        x != y ->
        (x, (v, y)) \In g ->
        x \notin loops g.
Proof.
move=>N I; apply/negP=>/In_loops1P[w]/(In_fun I) [_] E.
by rewrite E eqxx in N.
Qed.

Lemma loops1NPt x y z v :
        x \in loops (pts y (v, z)) ->
        x = y /\ y = z.
Proof. by case/In_loops1P=>w /InPt [][-> _]. Qed.

Lemma loops1Pt x y z v :
        y != 0 ->
        (x \in loops (pts y (v, z))) = (x == y) && (y == z) .
Proof.
move=>N; apply/In_loops1P/andP; first by case=>w/InPt [][-> _ /eqP].
by case=>/eqP -> /eqP <-; exists v; apply/In_condPt.
Qed.

Lemma In_loops1NE x y v :
        x != y ->
        loops (pts x (v, y)) =i [::].
Proof. by move/eqP=>N z; apply/In_loops1P=>-[w] /InPt [][->]. Qed.

(* other direction proved above for partial graphs *)
(* but this direction only holds for unary graphs *)

Lemma sub_preacyclic g :
        {subset cycles g <= loops g} ->
        preacyclic g.
Proof.
move=>S; apply/preacyclicP=>x y Dx Dy.
case: (x =P y)=>// /eqP Nxy /(bireach_cycleP _ Nxy) [xs] Y C.
have E : reach g x = [:: x].
- by apply/undup_uniq_eq1/loops1_reach/S/cyclesPCI/C/uniq_reach.
suff : y \in reach g x by rewrite E inE eq_sym (negbTE Nxy).
have : (y \in bireach g x) by apply/bireach_cycleP=>//; exists xs.
by rewrite mem_filter => /andP [].
Qed.

Lemma sub_preacyclicE g :
        preacyclic g = all [mem loops g] (cycles g).
Proof. by apply/idP/allP; [apply/preacyclic_sub|apply/sub_preacyclic]. Qed.

(* only one direction holds *)
Lemma preacyclicUn g1 g2 :
        valid (g1 \+ g2) ->
        preacyclic (g1 \+ g2) ->
        preacyclic g1 && preacyclic g2.
Proof.
move=>W /preacyclic_sub P; apply/andP; split; apply/sub_preacyclic;
by [apply: (cycles_loops_subL W)|apply: (cycles_loops_subR W)].
Qed.

(* this lemma doesn't genearlize to n-ary or partial graphs *)
Lemma closed_leaves_dangls0E g :
        closed g ->
        nilp (leaves g) ->
        nilp (dangls0 g).
Proof.
rewrite closed_dangls0E=>/allP /= S /nilP L; rewrite nilp_hasPn.
apply/hasPn=>x /[dup] Dgx; rewrite mem_filter=>/andP [/= Dx /sinksP [y Dy]].
rewrite adj_nxt // inE /eqP => N; suff {L} : y \in leaves g by rewrite L.
by rewrite leaves1E Dy -(eqP N); apply: S Dgx.
Qed.

Lemma preacyclic_mutation g x y z v :
        valid (pts x (v, y) \+ g) ->
        z \notin nodes (pts x (v, y) \+ g) ->
        preacyclic (pts x (v, y) \+ g) ->
        preacyclic (pts x (v, z) \+ g).
Proof.
move=>W Nz /preacyclic_sub /[dup] /(cycles_loops_subL W) Sl.
move=>/(cycles_loops_subR W) Sr; apply/sub_preacyclic=>w C.
have V : valid (pts x (v,z) \+ g) by rewrite (validPtUnE (v, y)).
have NxE : nxt (pts x (v, z) \+ g) x = z by rewrite nxt_ptsUn.
have NdE : nodes (pts x (v, y) \+ g) =i nodes (pts x (v, z) \+ g).
- by move=>r; rewrite !nodesPtUn.
have /cyclesNF : x \notin cycles (pts x (v, z) \+ g).
- by rewrite nxt_notin_cycles // NxE -NdE Nz.
by rewrite (freePtUn V) (loopsUn _ V) orbC=>/(_ _ C)/Sr=>->.
Qed.

Lemma path1_uniq g x y xs ys :
        uniq (y :: xs) ->
        uniq (y :: ys) ->
        path (edge g) x (rcons xs y) ->
        path (edge g) x (rcons ys y) ->
        xs = ys.
Proof.
elim: xs ys x y=>[|z zs IH] ys x y U1 U2 /= /andP [E1 P1] P2.
- case: ys E1 P2 U2=>//= z zs; rewrite inE negb_or -andbA.
  by move=>E1 /andP [] /(inj_edge E1) ->; rewrite eqxx.
case: ys U2 P2=>[|u us] U2 /= /andP [E2 P2].
- by rewrite (inj_edge E1 E2) /= inE eqxx in U1.
rewrite (inj_edge E1 E2) in P1 *.
by rewrite (IH _ _ _ _ _ P1 P2) // ?(uniqX U1, uniqX U2).
Qed.

Lemma cycle1_uniq g x xs ys :
        uniq (x :: xs) ->
        uniq (x :: ys) ->
        cycle (edge g) (x :: xs) ->
        cycle (edge g) (x :: ys) ->
        x :: xs = x :: ys.
Proof. by move=>U1 U2 P1 /(path1_uniq U1 U2 P1)=>->. Qed.

(* doesn't generalize to n-ary or partial graphs *)
Lemma cycle1_reachE g x xs :
        cycle (edge g) xs ->
        x \in xs ->
        reach g x =i xs.
Proof.
move=>C X y; apply/idP/idP; first by move/(cycle1_reach_sub C X).
move: (cycle_nodes C X)=>Dx; case/splitPr: X C=>p1 p2 /[swap].
rewrite mem_cat inE; case/or3P; last 2 first.
- by move/eqP=>->; rewrite reach0.
- case/splitPr=>p3 p4; rewrite -(cat1s x) -(cat1s y) cycle_catC catA /=.
  rewrite -catA /= -cat_rcons rcons_cat cat_path; case/andP=>P _.
  by apply/reachP; split=>//; exists (rcons p3 y); rewrite last_rcons.
case/splitPr=>p3 p4; rewrite cycle_catC -(cat1s y) !catA /=.
rewrite rcons_cat cat_path cats1; case/andP=>/= P _.
by apply/reachP; split=>//; exists (rcons (p2 ++ p3) y); rewrite last_rcons.
Qed.

(* doesn't generalize to n-ary or partial graphs *)
Lemma cycle1_mem_eq g x xs ys :
        cycle (edge g) xs ->
        cycle (edge g) ys ->
        x \in xs ->
        x \in ys ->
        xs =i ys.
Proof.
by move=>Cx Cy X Y y; rewrite -(cycle1_reachE Cx X) -(cycle1_reachE Cy Y).
Qed.

Lemma cycle_head_mem g xs x:
        cycle (edge g) xs ->
        x \in xs ->
        exists ys, [/\ cycle (edge g) (x :: ys),
                       uniq (x :: ys) & xs =i (x :: ys)].
Proof.
move=>C X; case: (cycle_head_uniq X C)=>ys [Cy Uy]; exists ys; split=>// y.
by rewrite -(cycle1_reachE C X) -(cycle1_reachE (x:=x) Cy) // inE eqxx.
Qed.

(* this lemma applies to unary graphs only *)
(* as proof depends on nodes being only in a single cycle *)
Lemma cycle1_brokenL2 g1 g2 x xs :
        x \in nodes g1 ->
        cycle (edge (g1 \+ g2)) (x :: xs) ->
        {subset xs <= [predC cycles g2]}.
Proof.
case: (normalP (g1 \+ g2))=>[-> _ /=|W].
- by rewrite rcons_path edge_undef andbF.
move=>Dx C y X; apply/cyclesXU=>-[ys][Cy Y _].
have : y \in x :: xs by rewrite inE X orbT.
case/(cycle_head_mem C)=>zs [{}C U Eqs].
have {}X : x \in y :: zs by rewrite -Eqs inE eqxx.
case: (cycle_head_mem Cy Y)=>us [Cu Uu Uus].
rewrite (cycle1_uniq U Uu C (sub_path (subrel_edgeR W) Cu)) in X.
by apply/dom_inNRX/Dx/(cycle_nodes Cu)/X/W.
Qed.

Lemma cycle_brokenL g1 g2 x xs :
        x \in nodes g1 ->
        cycle (edge (g1 \+ g2)) (x :: xs) ->
        cycle (edge g1) (x :: xs) \/
        exists y, [/\ y \in xs, y \in nodes g2,
                      y \in dangls0 g1 & y \notin cycles g2].
Proof.
case: (normalP (g1 \+ g2))=>[->|W] /=.
- by rewrite rcons_path edge_undef andbF.
move=>Dx1 /[dup] P /(path_broken Dx1) [P1|[y][z][Dy1 Ys Dz2 Rz Az1 Dlz1]];
first by [left]; rewrite mem_rcons inE in Rz; right; exists z.
case: eqP Rz Dz2 (dom_inNL W Dx1)=>[-> _ ->//|/=_ Rz Dz2 _].
by split=>//; apply: (cycle1_brokenL2 Dx1 P).
Qed.

Lemma cycle_brokenR g1 g2 x xs :
        x \in nodes g2 ->
        cycle (edge (g1 \+ g2)) (x :: xs) ->
        cycle (edge g2) (x :: xs) \/
        exists y, [/\ y \in xs, y \in nodes g1,
                      y \in dangls0 g2 & y \notin cycles g1].
Proof. by rewrite joinC; apply: cycle_brokenL. Qed.

End UnaryLemmas.

(***********)
(* Summit1 *)
(***********)

(* specializing summit to unary graphs *)

Definition summit1 {A} (g : unary_graph A) x := head null (summit g x).

Section Summit1Lemmas.
Context {A : Type}.
Implicit Type g : unary_graph A.

Lemma summit1_size g x : size (summit g x) = 1.
Proof.
rewrite /summit; move: {-1}(size (nodes g)) (erefl (size (nodes g)))=>size.
elim: size g x=>[|n IH] g /= x // E; case: ifP=>// Dx.
by rewrite size_big_cat adj_nxt //= big_cons big_nil addn0 IH // size_domF // E.
Qed.

Lemma summit1E g x : summit g x = [:: summit1 g x].
Proof. by rewrite /summit1; case: (summit g x) (summit1_size g x)=>[|z []]. Qed.

Lemma summit1EX g x y :
        y = summit1 g x <-> summit g x = [:: y].
Proof. by rewrite /summit1; split=>-> //; apply: summit1E. Qed.

Lemma summit1EY g x y :
        y \in summit g x <-> y = summit1 g x.
Proof. by rewrite summit1EX summit1E inE; split=>[/eqP|[]] ->. Qed.

Lemma summit1P g x y :
        y = summit1 g x <->
        exists xs, [/\ path (edge g) x xs, uniq (x :: xs),
          y = nxt g (last x xs) &
          y \notin nodes g \/ y \in x :: xs].
Proof.
split=>[/summit1EX S|[xs][P U /eqP L H]]; last first.
- suff : y \in summit g x by rewrite summit1E inE=>/eqP.
  apply/summitP; exists xs; split=>//; case: ifPn (path_nodes0 P) L=>Dx.
  - by rewrite adj_nxt ?inE ?(subset_consLI _ (path_nodes P) (mem_last x xs)).
  by rewrite orbF nilpE=>/eqP ->; rewrite nxt_notin.
have : y \in summit g x by rewrite S inE.
case/summitP=>xs [P U Ax H]; exists xs; split=>//; apply/eqP.
case: ifPn Ax (path_nodes0 P)=>[Dx|Dx /eqP ->]; last first.
- by rewrite orbF nilpE=>/eqP ->; rewrite nxt_notin.
by rewrite adj_nxt ?inE ?(subset_consLI _ (path_nodes P) (mem_last x xs)).
Qed.

Lemma summit1X g x :
        exists xs, [/\ path (edge g) x xs, uniq (x :: xs),
          summit1 g x = nxt g (last x xs) &
          summit1 g x \notin nodes g \/ summit1 g x \in x :: xs].
Proof. by apply/summit1P. Qed.

Lemma summit1Pt v x y:
        x != 0 ->
        summit1 (pts x (v, y) : unary_graph A) x = y.
Proof. by move=>N; rewrite /summit1 summitPt N. Qed.

Lemma summit1_notin g x :
        x \notin nodes g ->
        summit1 g x = x.
Proof. by rewrite /summit1; move/summit_notin=>->. Qed.

Lemma summit1_dangl g x :
        x \in nodes g ->
        nxt g x \notin nodes g ->
        summit1 g x = nxt g x.
Proof. by move=>??; apply/esym/summit1P; exists [::]; split=>//; left. Qed.

Lemma summit1_leaves g x :
        x \in leaves g ->
        summit1 g x = null.
Proof.
rewrite leaves1E=>/andP [Dx /eqP/[dup] N <-]; apply: (summit1_dangl Dx).
by rewrite N cond_dom.
Qed.

Lemma summit1_loops g x :
         x \in loops g ->
         summit1 g x = x.
Proof.
rewrite loops1E nodes_kfilt=>/andP [Dx] /eqP N.
by apply/esym/summit1P; exists [::]; split=>//; right; rewrite inE.
Qed.

End Summit1Lemmas.

(************)
(* Summits1 *)
(************)

(* specializing summits to unary graphs *)

Section Summits1Lemmas.
Context {A : Type}.
Implicit Type g : unary_graph A.

Lemma summits1E g : summits g = map (summit1 g) (nodes g).
Proof.
rewrite /summits/summit1; elim: (nodes g)=>[|x xs IH] //=.
by rewrite IH; case: (summit g x) (summit1_size g x)=>// z [].
Qed.

Lemma summit1_in_summits g x :
        x \in nodes g ->
        summit1 g x \in summits g.
Proof. by move=>Dx; rewrite summits1E; apply/mapP; exists x. Qed.

(* doesn't generalize to n-ary *)
(* because summits can be null even if there's no leaves *)
Lemma closed_leaves_summits1_sub g :
        closed g ->
        nilp (leaves g) ->
        {subset summits g <= cycles g}.
Proof.
move=>S L x; rewrite summits_cycles_dangls0E=>/orP [] //.
by rewrite (nilP (closed_leaves_dangls0E S L)).
Qed.

(* doesn't hold for n-ary graphs *)
Lemma summits1_nullX g :
        null \in summits g ->
        exists x, x \in leaves g.
Proof.
rewrite summits1E=>/mapP [x Dx] /summit1P [xs][P U L _].
exists (last x xs); rewrite leaves1E -L andbT.
by apply/subset_consLI/mem_last/path_nodes/P/Dx.
Qed.

Lemma leaves1_nilE g :
        (null \notin summits g) =
        (leaves g == [::]).
Proof.
apply/idP/idP=>[Nc|/eqP L]; last by apply/negP=>/summits1_nullX [x]; rewrite L.
apply: contraR Nc; case/has_nilP/hasP=>x /[dup]/leavesD Dx /summit1_leaves C.
by move: C (summit1_in_summits Dx)=>->.
Qed.

Lemma summit1_nxt g x y:
        preacyclic g ->
        (y == summit1 g (nxt g x)) = (y == summit1 g x).
Proof.
move/preacyclic_sub=>P; case: (nxt g x =P x)=>[->//|/eqP N].
have Dx: x \in nodes g by apply: contraR N=>/nxt_notin/eqP.
apply/eqP/eqP; last first.
- move/[dup]=>Ctr /summit1P [[|z zs]].
  - by case=>??-> [D|]; [apply/esym/summit1_notin|rewrite inE (negbTE N)].
  case=>/= /andP [+ Pth] /and3P [U1 U2 U3] L H.
  rewrite edge_adj adj_nxt // inE=>/andP [_ /eqP Nxtz].
  apply/summit1P; exists zs; rewrite -Nxtz; split=>//; first by apply/andP.
  case: H Ctr=>[->|]; first by left.
  rewrite inE=>/orP [/eqP -> Ctr|->]; last by right.
  have: x \in loops g.
  - by rewrite P // -in_nodes_summitsE // Ctr summit1_in_summits.
  by rewrite loops1E nodes_kfilt -!topredE /= eq_sym (negbTE N) andbF.
case/summit1P=>xs [Pth /= U L H].
have [NxtD|NxtD] := boolP (nxt g x \in nodes g); last first.
- rewrite (summit1_dangl Dx NxtD).
  by case/orP: (path_nodes0 Pth) NxtD L=>[/nilP -> /nxt_notin|] ->.
apply/summit1P; exists (nxt g x :: xs); split=>//=; last 1 first.
- by rewrite inE; case: H=>[->|->]; [left|right]; rewrite ?orbT.
- by rewrite edge_adj adj_nxt // NxtD inE eqxx Pth.
rewrite inE negb_or eq_sym N U andbT /=; apply/negP=>X.
suff : x \in loops g.
- by rewrite loops1E nodes_kfilt Dx -topredE /= eq_sym (negbTE N).
apply/P; rewrite cycles1E; apply/reachP; split=>//.
case/splitPr: X Pth=>p1 p2; rewrite -(cat1s x) catA cat_path /= cats1.
by case/andP; exists (rcons p1 x); rewrite last_rcons.
Qed.

Lemma summits1Eq_subL g1 g2 :
        valid (g1 \+ g2) ->
        summits g1 =i summits g2 ->
        {subset cycles g1 <= dangls0 g2}.
Proof.
move=>V C x /[dup]/cyclesD Dx /cycles_summits_sub; rewrite C.
by rewrite -notin_nodes_summitsE // (dom_inNL V Dx).
Qed.

Lemma summits1Eq_subR g1 g2 :
        valid (g1 \+ g2) ->
        summits g1 =i summits g2 ->
        {subset cycles g2 <= dangls0 g1}.
Proof. by rewrite joinC=>V C; apply: summits1Eq_subL. Qed.

Lemma summits1Eq_cyclesUn g1 g2 x :
        summits g1 =i summits g2 ->
        x \in cycles (g1 \+ g2) ->
        (x \in cycles g1) || (x \in cycles g2).
Proof.
case: (normalP (g1 \+ g2))=>[->|W]; first by rewrite cycles_undef.
move=>E /[dup] /cyclesPC [xs C] /cyclesD; rewrite domUnE //.
case/orP=>Dx.
- case/(cycle_brokenL Dx): C=>[/cyclesPCI ->//|[y][X Dy2 Dly1 Cny2]].
  move/dangls0_summits_sub: Dly1; rewrite E summits_cycles_dangls0E.
  by rewrite (negbTE Cny2) (negbTE (disjointR dangls0_nodesD _ Dy2)).
case/(cycle_brokenR Dx): C=>[/cyclesPCI ->|[y][X Dy1 Dly2 Cny1]].
- by rewrite orbT.
move/dangls0_summits_sub: Dly2; rewrite -E summits_cycles_dangls0E.
by rewrite (negbTE Cny1) (negbTE (disjointR dangls0_nodesD _ Dy1)).
Qed.

Lemma summits1EqUnL g1 g2 :
        valid (g1 \+ g2) ->
        summits g1 =i summits g2 ->
        summits (g1 \+ g2) =i summits g1.
Proof.
move=>V C x; rewrite !summits_cycles_dangls0E; apply/idP/idP; last first.
- case/orP=>[/(cyclesUnL V) ->//|Dl1].
  have [Dx2|Dnx2] := boolP (x \in nodes g2); last first.
  - by rewrite dangls0Un // 2!mem_filter /= Dl1 Dnx2 orbT.
  move/dangls0_summits_sub: Dl1; rewrite C in_nodes_summitsE //.
  by move/(cyclesUnR V)=>->.
case/orP.
- move/[dup]=>Cx /cyclesD; rewrite domUnE // => Dx.
  case/orP: (summits1Eq_cyclesUn C Cx)=>[->//|].
  case/orP: Dx=>Dx; first by move/cyclesD/(dom_inNLX V Dx).
  by move/(summits1Eq_subR V C)=>->; rewrite orbT.
move/[dup]=>/(disjointL dangls0_nodesD) Dnx.
rewrite dangls0Un // 2!mem_filter /=.
case/orP=>[/andP [_ ->]|]; first by rewrite orbT.
by case/andP=>_ /dangls0_summits_sub; rewrite -C summits_cycles_dangls0E.
Qed.

End Summits1Lemmas.


(***************)
(* Partitioned *)
(***************)

(* when summits are loops (no dangls) *)
(* the graph is divided into disjoint equivalence classes of nodes *)
(* determined by the loop into which any given node summits *)
(* this concept is used in union-find *)

Definition partitioned1 {A} (g : unary_graph A) :=
  {subset summits g <= loops g}.

Section PartitionedLemmas.
Context {A : Type}.
Implicit Type g : unary_graph A.

Lemma part_closed g :
        partitioned1 g ->
        closed g.
Proof.
by move=>P; apply/summits_closed0=>x /P/loopsD Dx; rewrite inE Dx orbT.
Qed.

Lemma part_leaves g :
        partitioned1 g ->
        nilp (leaves g).
Proof.
by rewrite nilpE -leaves1_nilE=>S; apply/negP=>/S/loopsD; rewrite mem_dom0.
Qed.

Lemma part_preacyclic g :
        partitioned1 g ->
        preacyclic g.
Proof. by move=>S; apply/sub_preacyclic=>x /cycles_summits_sub/S. Qed.

Lemma part_char g :
        partitioned1 g ->
        [/\ closed g, preacyclic g & nilp (leaves g)].
Proof.
by move=>P; split; [apply/part_closed|apply/part_preacyclic|apply/part_leaves].
Qed.

Lemma part_summits1E g :
        partitioned1 g ->
        summits g =i loops g.
Proof. by move=>P x; apply/idP/idP; [apply/P|apply/loops_summits_sub]. Qed.

Lemma part_loop_eta g x :
        partitioned1 g ->
        x \in summits g ->
        exists v, g = pts x (v, x) \+ free g x.
Proof. by move=>P /P/In_loops1P [v] In; exists v; apply: graph_eta. Qed.

Lemma loops_eta g x :
        x \in loops g ->
        exists v, g = pts x (v, x) \+ free g x.
Proof. by move/In_loops1P=> [v] In; exists v; apply: graph_eta. Qed.

Lemma partUn g1 g2 :
        valid (g1 \+ g2)->
        partitioned1 g1 ->
        partitioned1 g2 ->
        partitioned1 (g1 \+ g2).
Proof.
move=>V /part_char [C1 P1 L1] /part_char [C2 P2 L2].
move: (preacyclic_sub (P1)) (preacyclic_sub (P2))=>S1 S2.
move: (closed_preacyclicUn C1 C2 P1 P2)=>P /= x.
rewrite summitsUn // !mem_filter //=.
case/orP=>/andP [Dnx].
- by rewrite loopsUn // => /(closed_leaves_summits1_sub C1 L1)/S1 ->.
by rewrite loopsUn // orbC => /(closed_leaves_summits1_sub C2 L2)/S2 ->.
Qed.

Lemma part_summits1_free g x :
        x \in loops g ->
        {subset summits (free g x) <= summits g}.
Proof.
rewrite {1 3}(kfiltC g (pred1 x))=>/[dup] Ls /loopsD/[dup] Dx /dom_valid V y.
rewrite !summits1E=>/mapP [z]; rewrite -kfiltC1=>Dz Ez; apply/mapP; exists z.
- by rewrite domUnE // Dz orbT.
case/summit1P: Ez=>xs [P //= /andP [U1 U2] L H]; apply/summit1P.
have P' : path (edge (kfilt g (pred1 x) \+ kfilt g (predC (pred1 x)))) z xs.
- by rewrite -{1}kfiltC; apply/sub_path/P/edge_kfilt_sub.
move/path_nodes: P=>Sb; move: (mem_last z xs) (subset_consLI Dz Sb)=>M S.
have Lzl : last z xs \in nodes (kfilt g (predC1 x)) by apply: S.
have Lz : last z xs \in nodes (kfilt g (pred1 x) \+ kfilt g (predC1 x)).
- by rewrite domUnE // S // orbT.
have Ey: y = nxt (kfilt g (pred1 x) \+ kfilt g (predC1 x)) (last z xs).
- by rewrite /nxt adjUnR // ifT.
case: (x =P y)=>[E|/eqP N]; last first.
- exists xs; split=>//=; first by rewrite U1 U2.
  case: H=>H; [left|by right].
  by rewrite domUnE // negb_or H nodes_kfilt negb_and inE eq_sym N orbT.
exists (rcons xs x); subst x; split=>//=; last 2 first.
- by move: Ls; rewrite loops1E nodes_kfilt last_rcons=>/andP [_ /eqP].
- by right; rewrite inE mem_rcons inE eqxx orbT.
- by rewrite rcons_path P' edge_adj Dx adjUnR //= ifT // adj_nxt // inE -L.
rewrite mem_rcons inE negb_or U1 rcons_uniq U2 !andbT; apply/andP; split.
- by case: eqP Dz=>// ->; rewrite kfiltC1 domF eqxx.
by apply/negP=>/Sb; rewrite kfiltC1 domF eqxx.
Qed.

End PartitionedLemmas.


(*********************)
(* Spatial predicate *)
(*********************)

(* layout for unary graphs *)

Definition node1_lay {A} x (v : A * node) : heap :=
  x :-> v.1 \+ x.+1 :-> v.2.

Lemma dom_node1lay {A} x y (v : A * node)  :
        x \in dom (node1_lay y v) ->
        y <= x.
Proof.
rewrite domPtUn inE=>/andP [_]; case: (y =P x)=>[<-|_] //=.
by rewrite domPt inE /= =>/eqP <-; elim: y.
Qed.

Lemma node1layK {A} x (v1 v2 : A * node) :
        valid (node1_lay x v1) ->
        node1_lay x v1 = node1_lay x v2 ->
        v1 = v2.
Proof.
case: v1=>a1 n1; case: v2=>a2 n2.
rewrite /node1_lay=>/= V.
by case/(hcancelV V)=><- {}V; move/(hcancelPtV V)=><-.
Qed.

Lemma node1layV {A} x (v : A * node) :
        valid (node1_lay x v) = (x != null).
Proof.
rewrite /node1_lay.
case: (x =P null)=>[->|/eqP N]; first by rewrite validUnAE validPt.
by rewrite !validPtUn !inE N /= -addn1 -{1}(addn0 x) eqn_add2l.
Qed.

(* layout of unary graph in a heap *)
(* the wrapping conditional is to make graph1_lay *)
(* validity imply validity of g, which frees lemmas *)
(* from dragging excessive validity conditions *)
Definition graph1_lay {A} (g : unary_graph A) : heap :=
  if valid g then
    \big[join/Unit]_(xv <- assocs g) node1_lay xv.1 xv.2
  else undef.

Lemma graph1lay_sub {A} (g : unary_graph A) :
        valid (graph1_lay g) ->
        {subset nodes g <= dom (graph1_lay g)}.
Proof.
move=>V x /[dup] Dx /In_domX [v] /In_assocs Ax.
rewrite /graph1_lay (dom_valid Dx) in V *.
rewrite big_domUnE //=; apply: hasPInX Ax _.
by rewrite domPtUn inE node1layV (dom_cond Dx) eqxx.
Qed.

Lemma graph1layV {A} (g : unary_graph A) :
        reflect (valid g /\
                 forall x, x \in nodes g ->
                   x.+1 \notin nodes g)
                (valid (graph1_lay g)).
Proof.
have N1 x : x != x.+1 by rewrite -{1}(addn0 x) -addn1 eqn_add2l.
apply: (iffP idP)=>[V|[Vg H]].
- split=>[|x Dx]; first by rewrite /graph1_lay in V; case: ifP V.
  rewrite /graph1_lay/node1_lay big_assocs_dom
    (bigD1FE x) (dom_valid Dx) Dx in V.
  case: dom_find Dx V=>//= v _ _ _ V.
  - rewrite (bigD1FE x.+1) domF eq_sym (negbTE (N1 x)) in V.
    by case: dom_find V=>//= v1 _ _; rewrite invalidX.
rewrite /graph1_lay Vg; apply: big_validV2I=>/=.
- exact: Uniq_assocs.
- by case=>x v /In_assocs X; rewrite node1layV (In_cond X).
case=>x vx [y vy] /In_assocs Hx /In_assocs Hy N /=.
have Nxy : x != y by case: eqP Hy N=>// <- /(In_fun Hx) ->.
rewrite validUnAE !node1layV (In_cond Hx) (In_cond Hy) /=.
apply/allP=>/= z.
rewrite !domUn !inE !domPt !inE !validPt2 !N1 !andbT /=.
rewrite (In_cond Hx) (In_cond Hy) /= negb_or.
case/orP=>[/eqP <-|/eqP ->].
- by rewrite Nxy; case: eqP Hy (H _ (In_dom Hx))=>// -> /In_dom ->.
rewrite !eqSS (eq_sym y) Nxy andbT.
by case: eqP Hx (H _ (In_dom Hy))=>// -> /In_dom ->.
Qed.

Lemma graph1layVI {A} (g : unary_graph A) :
        valid (graph1_lay g) ->
        valid g.
Proof. by case/graph1layV. Qed.

(* key lemma to characterize the pointers in graph1_lay *)
(* must by proved by um_indf, because it relies on *)
(* induction that traverses g in the order of sorting *)
Lemma dom_graph1lay {A} (g : unary_graph A) :
        valid (graph1_lay g) ->
        dom (graph1_lay g) =
        \big[cat/[::]]_(x <- nodes g) [:: x; x.+1].
Proof.
rewrite /graph1_lay big_assocs_dom.
elim/um_indf: g=>[||/= y w g IH V /(order_path_min trans) Ag] //=.
- by rewrite dom0 !big_nil.
rewrite !(validX V) in IH *.
have L1 z : ord z z.+1 by rewrite /ord /=.
rewrite domPtUnK // !big_cons findPtUn //= => Vg.
set h := (X in _ \+ X) in Vg *.
have Vh : valid h by rewrite (validR Vg).
have E : h = \big[join/Unit]_(x <- nodes g)
  if find x g is Some v then node1_lay x v else undef.
- apply: eq_Bigr=>x /mem_seqP Dx _.
  rewrite findPtUn2 //; case: (x =P y) Dx=>// ->.
  by rewrite (negbTE (validPtUnD V)).
rewrite -E in IH; move: (IH Vh)=>{}IH; rewrite -IH.
have Eg : graph1_lay g = h by rewrite /graph1_lay (validR V) big_assocs_dom.
have Wg : valid (graph1_lay g) by rewrite Eg.
have Y : forall x, x \in nodes g -> y < x by move/allP: Ag; apply.
have Y1 : forall x, x \in nodes g -> y.+1 < x.
- move=>x Dx; rewrite ltnNge leq_eqVlt negb_or -ltnNge ltnS Y // andbT.
  case: eqP Dx=>// -> /(graph1lay_sub Wg); rewrite Eg.
  by move/(contraL validPtUnD)=>/(_ (idyn w.1)); rewrite (validX Vg).
(* lifting Y, Y1 from nodes g to dom h *)
suff [X X1] : [/\ all (ord y) (dom h) & all (ord y.+1) (dom h)].
- by rewrite -!joinA !domPtUnK ?(validX Vg) //= L1.
by split; apply/allP=>z; rewrite big_domUn inE (validX Vh) /=;
case/hasP=>x Dx; rewrite findPtUn2 //;
case: (x =P y) Dx (validPtUnD V)=>[<- ->//|_];
case: (dom_find x g)=>// v /In_find/In_dom /= Dx _ _ _ /dom_node1lay;
apply: leq_trans; [apply: Y|apply: Y1].
Qed.

(* morphism-style properties *)

Lemma graph1lay0 {A} : graph1_lay (Unit : unary_graph A) = Unit.
Proof. by rewrite /graph1_lay assocs0 big_nil. Qed.

Lemma graph1lay_undef {A} : graph1_lay (undef : unary_graph A) = undef.
Proof. by []. Qed.

Lemma graph1layPt {A} x (v : A * node) :
        graph1_lay (pts x v) = node1_lay x v.
Proof.
rewrite /graph1_lay/node1_lay assocsPt validPt /=.
case: (x =P 0)=>[->|_] /=; first by rewrite pts_condN.
by rewrite big_cons big_nil unitR.
Qed.

Lemma graph1layUn {A} (g1 g2 : unary_graph A) :
        graph1_lay (g1 \+ g2) = graph1_lay g1 \+ graph1_lay g2.
Proof.
case: (normalP (g1 \+ g2))=>[E|V]; last first.
- rewrite /graph1_lay !big_assocs_dom !(validX V) /=.
  rewrite (perm_big _ (perm_domUn V)) big_cat /=.
  by congr (_ \+ _); apply: eq_Bigr=>x /mem_seqP Dx _;
  [rewrite findUnL ?Dx|rewrite findUnR ?Dx].
rewrite E graph1lay_undef /graph1_lay.
case: ifP=>Vg1; last by rewrite undef_join.
case: ifP=>Vg2; last by rewrite join_undef.
set h1 := (X in X \+ _); set h2 := (X in _ \+ X).
case: (normalP (h1 \+ h2))=>//; case: validUn=>// Vh1 Vh2 Dh _.
have V1 : valid (graph1_lay g1) by rewrite /graph1_lay Vg1 Vh1.
have V2 : valid (graph1_lay g2) by rewrite /graph1_lay Vg2 Vh2.
have : ~~ valid (g1 \+ g2) by rewrite E.
rewrite validUnAE Vg1 Vg2 /=.
case/allPn=>x Dx2 /=; rewrite negbK=>Dx1.
move: (graph1lay_sub V1 Dx1) (graph1lay_sub V2 Dx2).
rewrite /graph1_lay Vg1 Vg2=>Dh1 Dh2.
by move: (Dh x Dh1); rewrite Dh2.
Qed.

Lemma graph1layPtUn {A} x (v : A * node) (g : unary_graph A) :
        graph1_lay (pts x v \+ g) = node1_lay x v \+ graph1_lay g.
Proof. by rewrite graph1layUn graph1layPt. Qed.

(* graph1lay isn't a PCM morphism formally *)
(* because it doesn't preserve validity *)
(* as valid inputs can map to invalid outputs *)
(* Lemma graph1lay_is_pcm_morphism A : pcm_morph_axiom relT (@graph1_lay A). *)
(* Proof. *)
(* Abort. *)

(* spatial predicate definition and properties *)

Definition node1 {A} x (v : A * node) : Pred heap :=
  eq^~ (node1_lay x v).
Definition graph1 {A} (g : unary_graph A) : Pred heap :=
  eq^~ (graph1_lay g).

(* the layout determines the graph *)
(* proof uses dom_graph2lay and um_indf *)
(* to set up induction that depends on node ordering *)
Lemma graph1K {A} (g1 g2 : unary_graph A) h :
        valid h ->
        h \In graph1 g1 ->
        h \In graph1 g2 ->
        g1 = g2.
Proof.
move/[swap]=>-> V1; rewrite /graph1=>E.
have V2 : valid (graph1_lay g2) by rewrite -E.
move: (graph1layVI V1) (graph1layVI V2)=>Vg1 Vg2.
have : dom (graph1_lay g1) = dom (graph1_lay g2) by rewrite E.
rewrite !dom_graph1lay //; elim/um_indf: g1 g2 E Vg1 V1 Vg2 V2=>
[||x xs g1 IH V /(order_path_min trans) Ag] g2 E Vg1 V1 Vg2 V2.
- by rewrite big_nil; elim/um_indf: g2 E Vg2 V2.
- rewrite big_nil; elim/um_indf: g2 {E} Vg2 V2=>
  [||y ys g2 _ V /(order_path_min trans) Ag2] // Vg2 V2.
  by rewrite domPtUnK //= big_cons.
rewrite domPtUnK //= big_cons; elim/um_indf: g2 E V2 Vg2=>
[||y ys g2 IH2 W /(order_path_min trans) Ag2] E V2 Vg2.
- by rewrite big_nil.
- by rewrite big_nil.
rewrite domPtUnK // big_cons; case=>? _; subst y.
rewrite !graph1layPtUn // -!joinA in V1 V2 E.
case/(hcancelV V1): E=>E1 {}V1 /(hcancelV V1) [E2 {}V1] _ /IH -> //.
- by rewrite (validR Vg1).
- by rewrite (validR Vg2).
- by rewrite (validX V2).
by rewrite (prod_eta xs) E1 E2 -prod_eta.
Qed.

Lemma graph10 {A} : graph1 (Unit : unary_graph A) <~> emp.
Proof. by rewrite /graph1 graph1lay0. Qed.

Lemma graph1_undef {A} :
        graph1 (undef : unary_graph A) <~> eq^~ undef.
Proof. by rewrite /graph1 graph1lay_undef. Qed.

Lemma graph1Pt {A} x (v : A * node) :
        graph1 (pts x v) <~> node1 x v.
Proof. by rewrite /graph1 graph1layPt. Qed.

Lemma graph1Un {A} (g1 g2 : unary_graph A) :
        graph1 (g1 \+ g2) <~> graph1 g1 # graph1 g2.
Proof.
move=>h; split=>[->|[h1][h2][->{h}] ->->]; last by rewrite -graph1layUn.
by exists (graph1_lay g1), (graph1_lay g2); rewrite graph1layUn.
Qed.

Lemma graph1PtUn {A} x v (g : unary_graph A) :
        graph1 (pts x v \+ g) <~> node1 x v # graph1 g.
Proof. by rewrite graph1Un graph1Pt. Qed.

Lemma In_graph1_eta {A} (g : unary_graph A) x (v : A * node) :
        (x, v) \In g ->
        graph1 g <~> node1 x v # graph1 (free g x).
Proof. by move/In_eta=>E; rewrite {1}E graph1PtUn. Qed.

Lemma In_graph1V {A} (g : unary_graph A) h :
        h \In graph1 g ->
        valid h ->
        valid g.
Proof. by move=>->/graph1layVI. Qed.

Lemma In_graph1V2 {A} (g1 g2 : unary_graph A) h1 h2 :
        h1 \In graph1 g1 ->
        h2 \In graph1 g2 ->
        valid (h1 \+ h2) ->
        valid (g1 \+ g2).
Proof. by move=>H1 H2 /In_graph1V; apply; rewrite graph1Un; exists h1, h2. Qed.


(*****************)
(*****************)
(* Binary graphs *)
(*****************)
(*****************)

(* notation for left/right node of x *)
Definition lft A (g : binary_graph A) x := oapp (fst \o snd) null (find x g).
Definition rgh A (g : binary_graph A) x := oapp (snd \o snd) null (find x g).

(* update left link of binary graph *)
Abbreviation upd2L x l g := (updg x (fun '(a, v) => (a, (l, v.2))) g).
(* update right link of binary graph *)
Abbreviation upd2R x r g := (updg x (fun '(a, v) => (a, (v.1, r))) g).
(* update contents and left link of binary graph *)
Abbreviation upd2CL x a l g := (updg x (fun '(_, v) => (a, (l, v.2))) g).
(* update contents and right link of binary graph *)
Abbreviation upd2CR x a r g := (updg x (fun '(_, v) => (a, (v.1, r))) g).

Section BinGraphLemmas.
Context {A : Type}.
Implicit Type g : binary_graph A.

(* structural properties *)

CoInductive bingraph_spec g x :
    bool -> node -> node -> seq node -> Type :=
| bingraph_notin of x \notin nodes g :
    bingraph_spec g x false null null [::]
| bingraph_in v xs of (x, (v, xs)) \In g :
    bingraph_spec g x true xs.1 xs.2 [:: xs.1; xs.2].

Lemma In_graph2X g x :
        bingraph_spec g x (x \in nodes g) (lft g x) (rgh g x) (adj g x).
Proof.
rewrite /adj/lft/rgh; case: dom_find=>[/In_findN|[k v] /In_find H _].
- by apply: bingraph_notin.
by apply: bingraph_in H.
Qed.

Lemma In_graph2 g {x v xs} :
        (x, (v, xs)) \In g ->
        xs = (lft g x, rgh g x).
Proof.
move/[dup]/In_dom; case: In_graph2X=>// k [l r] H _.
by case/(In_fun H)=>_ <-.
Qed.

Lemma adj2E g x :
        adj g x =
        if x \in nodes g then [:: lft g x; rgh g x] else [::].
Proof. by case: In_graph2X. Qed.

Lemma In_sinks2 g {x v xs} :
        (x, (v, xs)) \In g ->
        (xs.1 \in sinks g) * (xs.2 \in sinks g).
Proof.
move/[dup]=>H /In_graph E; split; apply/sinksPA; exists x;
case: In_graph2X E=>//= _ _ /(In_fun H) [_ <-] _;
by rewrite !inE eqxx // orbT.
Qed.

(* interaction with node update *)

Lemma lftUg x y f g :
        lft (updgf x f g) y =
        if find x g is Some v then
          if y == x then (f v).2.1
          else lft g y
        else null.
Proof. by rewrite /lft findUg; case: (find x g); case: (y =P x). Qed.

Lemma rghUg x y f g :
        rgh (updgf x f g) y =
        if find x g is Some v then
          if y == x then (f v).2.2
          else rgh g y
        else null.
Proof. by rewrite /rgh findUg; case: (find x g); case: (y =P x). Qed.

(* interaction with union/pts *)

Lemma lft_undef x : lft (undef : binary_graph A) x = null.
Proof. by []. Qed.

Lemma rgh_undef x : rgh (undef : binary_graph A) x = null.
Proof. by []. Qed.

Lemma lft_unit x : lft (Unit : binary_graph A) x = null.
Proof. by []. Qed.

Lemma rgh_unit x : rgh (Unit : binary_graph A) x = null.
Proof. by []. Qed.

Lemma lftPt x y v :
        lft (pts x v) y =
        if valid (ptsT (binary_graph A) x v) && (y == x) then v.2.1
        else null.
Proof. by rewrite /lft findPt2 /= validPt andbC; case: ifP. Qed.

Lemma rghPt x y v :
        rgh (pts x v) y =
        if valid (ptsT (binary_graph A) x v) && (y == x) then v.2.2
        else null.
Proof. by rewrite /rgh findPt2 /= validPt andbC; case: ifP. Qed.

Lemma lftPtUn g x y v :
        lft (pts x v \+ g) y =
        if valid (pts x v \+ g) then
          if y == x then v.2.1 else lft g y
        else null.
Proof.
case: (normalP (pts x v \+ _))=>[->//|V].
by rewrite /lft findPtUn2 //=; case: eqP.
Qed.

Lemma rghPtUn g x y v :
        rgh (pts x v \+ g) y =
        if valid (pts x v \+ g) then
          if y == x then v.2.2 else rgh g y
        else null.
Proof.
case: (normalP (pts x v \+ _))=>[->//|V].
by rewrite /rgh findPtUn2 //=; case: eqP.
Qed.

Lemma lftF g x y :
        lft (free g x) y = if y == x then null else lft g y.
Proof. by rewrite /lft findF; case: eqP. Qed.

Lemma rghF g x y :
        rgh (free g x) y = if y == x then null else rgh g y.
Proof. by rewrite /rgh findF; case: eqP. Qed.

(* interaction with other primitives *)

Lemma lft_erase g x : lft (erase g) x = lft g x.
Proof. by rewrite /lft find_erase; case: (find x g). Qed.

Lemma rgh_erase g x : rgh (erase g) x = rgh g x.
Proof. by rewrite /rgh find_erase; case: (find x g). Qed.

Lemma lft_kfilt g p x :
        lft (kfilt g p) x = if x \in p then lft g x else null.
Proof. by rewrite /lft find_kfilt; case: ifP. Qed.

Lemma rgh_kfilt g p x :
        rgh (kfilt g p) x = if x \in p then rgh g x else null.
Proof. by rewrite /rgh find_kfilt; case: ifP. Qed.

End BinGraphLemmas.

Section BinGraphMap.
Context {A B : Type}.
Implicit Type f : node -> A * (node * node) -> B * (node * node).
Implicit Type g : binary_graph A.

Lemma lft_graphmap f g x :
        lft (graph_map f g) x =
        if find x g is Some v then (f x v).2.1 else null.
Proof. by rewrite /lft find_graphmap; case: (find x g). Qed.

Lemma rgh_graphmap f g x :
        rgh (graph_map f g) x =
        if find x g is Some v then (f x v).2.2 else null.
Proof. by rewrite /rgh find_graphmap; case: (find x g). Qed.

End BinGraphMap.

Section BinGraphCfilt.
Context {A : eqType}.
Implicit Type g : binary_graph A.

Lemma lft_cfilt g xs x :
        lft (cfilt g xs) x =
        if find x g is Some v then
          if v.1 \in xs then v.2.1 else null
        else null.
Proof. by rewrite /lft find_cfilt; case: (find x g)=>//= v; case: ifP. Qed.

Lemma rgh_cfilt g xs x :
        rgh (cfilt g xs) x =
        if find x g is Some v then
          if v.1 \in xs then v.2.2 else null
        else null.
Proof. by rewrite /rgh find_cfilt; case: (find x g)=>//= v; case: ifP. Qed.

End BinGraphCfilt.

Section BinGraphClosed.
Context {A : Type}.
Implicit Type g : binary_graph A.

Lemma In_closed2 x v xl xr g :
        (x, (v, (xl, xr))) \In g ->
        reflect [/\ xl \in nodes0 g, xr \in nodes0 g &
                    {subset sinks (free g x) <= nodes0 g}]
                (closed g).
Proof.
move=>H; case: (In_closed H).
- by case=>X1 X2; constructor; rewrite !X1 // !inE /= eqxx ?orbT.
move=>X; constructor; case=>Xl Xr S; apply: X.
by split=>// z; rewrite !inE /=; case/orP=>/eqP ->.
Qed.

Lemma closed2_links x v xl xr g :
        (x, (v, (xl, xr))) \In g ->
        closed g ->
        (xl \in nodes0 g) * (xr \in nodes0 g).
Proof. by move=>H /(In_closed2 H) []. Qed.

Lemma In_closed2PtUn x v xl xr g :
        x \in nodes g ->
        closed g ->
        closed (pts x (v, (xl, xr)) \+ free g x) =
        [&& xl \in nodes0 g & xr \in nodes0 g].
Proof.
move=>H C; case: (In_closedPtUn H C).
- by move=>S; rewrite !S // !inE /= eqxx ?orbT.
move=>X. apply/esym/negP=>/andP [H1 H2]; elim: X.
by move=>z; rewrite !inE /= =>/orP [] /eqP ->.
Qed.

End BinGraphClosed.

Arguments In_closed2PtUn {A x v xl xr g}.

(**********************)
(**********************)
(* Spatial predicates *)
(**********************)
(**********************)

(* layout for binary graphs *)

Definition node2_lay {A} x (v : A * (node * node)) : heap :=
  x :-> v.1 \+ (x.+1 :-> v.2.1 \+ x.+2 :-> v.2.2).

Lemma dom_node2lay {A} x y (v : A * (node * node))  :
        x \in dom (node2_lay y v) ->
        y <= x.
Proof.
rewrite domPtUn inE=>/andP [_]; case: (y =P x)=>[<-|_] //=.
rewrite domPtUn inE=>/andP [_]; case: (y.+1 =P x)=>[<-|_] //=.
by rewrite domPt inE /= =>/eqP <-; elim: y.
Qed.

Lemma node2layK {A} x (v1 v2 : A * (node * node)) :
        valid (node2_lay x v1) ->
        node2_lay x v1 = node2_lay x v2 ->
        v1 = v2.
Proof.
case: v1=>a1 [l1 r1]; case: v2=>a2 [l2 r2].
rewrite /node2_lay=>/= V.
by do 2![case/(hcancelV V)=><- {}V]; move/(hcancelPtV V)=><-.
Qed.

Lemma node2layV {A} x (v : A * (node * node)) :
        valid (node2_lay x v) = (x != null).
Proof.
rewrite /node2_lay.
case: (x =P null)=>[->|/eqP N]; first by rewrite validUnAE validPt.
rewrite !validPtUn !inE domPtUn !inE /= validPtUn inE /=.
rewrite negb_and negbK negb_or {}N andb_orr andNb /=.
by rewrite -addn2 -addn1 -{4 5}(addn0 x) !eqn_add2l.
Qed.

(* layout of binary graph in a heap *)
(* the wrapping conditional is to make graph2_lay *)
(* validity imply validity of g, which frees lemmas *)
(* from dragging excessive validity conditions *)
Definition graph2_lay {A} (g : binary_graph A) : heap :=
  if valid g then
    \big[join/Unit]_(xv <- assocs g) node2_lay xv.1 xv.2
  else undef.

Lemma graph2lay_sub {A} (g : binary_graph A) :
        valid (graph2_lay g) ->
        {subset nodes g <= dom (graph2_lay g)}.
Proof.
move=>V x /[dup] Dx /In_domX [v] /In_assocs Ax.
rewrite /graph2_lay (dom_valid Dx) in V *.
rewrite big_domUnE //=; apply: hasPInX Ax _.
by rewrite domPtUn inE node2layV (dom_cond Dx) eqxx.
Qed.

Lemma graph2layV {A} (g : binary_graph A) :
        reflect (valid g /\
                 forall x, x \in nodes g ->
                   x.+1 \notin nodes g /\
                   x.+2 \notin nodes g)
                (valid (graph2_lay g)).
Proof.
have N1 x : x != x.+1 by rewrite -{1}(addn0 x) -addn1 eqn_add2l.
have N2 x : x != x.+2 by rewrite -{1}(addn0 x) -addn2 eqn_add2l.
apply: (iffP idP)=>[V|[Vg H]].
- split=>[|x Dx]; first by rewrite /graph2_lay in V; case: ifP V.
  rewrite /graph2_lay/node2_lay big_assocs_dom
    (bigD1FE x) (dom_valid Dx) Dx in V.
  case: dom_find Dx V=>//= v _ _ _; split.
  - rewrite (bigD1FE x.+1) domF eq_sym (negbTE (N1 x)) in V.
    by case: dom_find V=>//= v1 _ _; rewrite invalidX.
  rewrite (bigD1FE x.+2) domF eq_sym (negbTE (N2 x)) in V.
  by case: dom_find V=>//= v2 _ _; rewrite invalidX.
rewrite /graph2_lay Vg; apply: big_validV2I=>/=.
- exact: Uniq_assocs.
- by case=>x v /In_assocs X; rewrite node2layV (In_cond X).
case=>x vx [y vy] /In_assocs Hx /In_assocs Hy N /=.
have Nxy : x != y by case: eqP Hy N=>// <- /(In_fun Hx) ->.
rewrite validUnAE !node2layV (In_cond Hx) (In_cond Hy) /=.
apply/allP=>/= z.
rewrite !domUn !inE !domPt !inE !domPt2 !inE /= !N1 /=.
rewrite (In_cond Hx) (In_cond Hy) /=.
case/andP=>Vy Dy; apply/negP=>/andP [Vx].
case/or3P: Dy=>[/eqP <-|/eqP ->|/eqP ->].
- rewrite (negbTE Nxy) /= => X.
  by case/orP: X Hy (H _ (In_dom Hx))=>/eqP <- /In_dom -> [].
- rewrite !eqSS (eq_sym y) (negbTE Nxy) /= => X.
  by case/orP: X Hx Hy (H _ (In_dom Hy)) (H _ (In_dom Hx))=>
  /eqP <-; [move/In_dom=>-> _ []|move=>_ /In_dom-> _ []].
rewrite !eqSS (eq_sym y) (negbTE Nxy) orbF => X.
by case/orP: X Hx Hy (H _ (In_dom Hy)) (H _ (In_dom Hx))=>
/eqP <- /In_dom -> _ [].
Qed.

Lemma graph2layVI {A} (g : binary_graph A) :
        valid (graph2_lay g) ->
        valid g.
Proof. by case/graph2layV. Qed.

(* key lemma to characterize the pointers in graph2_lay *)
(* must by proved by um_indf, because it relies on *)
(* induction that traverses g in the order of sorting *)
Lemma dom_graph2lay {A} (g : binary_graph A) :
        valid (graph2_lay g) ->
        dom (graph2_lay g) =
        \big[cat/[::]]_(x <- nodes g) [:: x; x.+1; x.+2].
Proof.
rewrite /graph2_lay big_assocs_dom.
elim/um_indf: g=>[||/= y w g IH V /(order_path_min trans) Ag] //=.
- by rewrite dom0 !big_nil.
rewrite !(validX V) in IH *.
have L1 z : ord z z.+1 by rewrite /ord /=.
have L2 z : ord z z.+2 by rewrite /ord /=.
rewrite domPtUnK // !big_cons findPtUn //= => Vg.
set h := (X in _ \+ X) in Vg *.
have Vh : valid h by rewrite (validR Vg).
have E : h = \big[join/Unit]_(x <- nodes g)
  if find x g is Some v then node2_lay x v else undef.
- apply: eq_Bigr=>x /mem_seqP Dx _.
  rewrite findPtUn2 //; case: (x =P y) Dx=>// ->.
  by rewrite (negbTE (validPtUnD V)).
rewrite -E in IH; move: (IH Vh)=>{}IH; rewrite -IH.
have Eg : graph2_lay g = h by rewrite /graph2_lay (validR V) big_assocs_dom.
have Wg : valid (graph2_lay g) by rewrite Eg.
have Y : forall x, x \in nodes g -> y < x by move/allP: Ag; apply.
have Y1 : forall x, x \in nodes g -> y.+1 < x.
- move=>x Dx; rewrite ltnNge leq_eqVlt negb_or -ltnNge ltnS Y // andbT.
  case: eqP Dx=>// -> /(graph2lay_sub Wg); rewrite Eg.
  by move/(contraL validPtUnD)=>/(_ (idyn w.1)); rewrite (validX Vg).
have Y2 : forall x, x \in nodes g -> y.+2 < x.
- move=>x Dx; rewrite ltnNge leq_eqVlt negb_or -ltnNge ltnS Y1 // andbT.
  case: eqP Dx=>// -> /(graph2lay_sub Wg); rewrite Eg.
  by move/(contraL validPtUnD)=>/(_ (idyn w.2)); rewrite (validX Vg).
(* lifting Y, Y1, Y2 from nodes g to dom h *)
suff [X X1 X2] : [/\ all (ord y) (dom h),
  all (ord y.+1) (dom h) & all (ord y.+2) (dom h)].
- by rewrite -!joinA !domPtUnK ?(validX Vg) //= ?L1 ?L2.
by split; apply/allP=>z; rewrite big_domUn inE (validX Vh) /=;
case/hasP=>x Dx; rewrite findPtUn2 //;
case: (x =P y) Dx (validPtUnD V)=>[<- ->//|_];
case: (dom_find x g)=>// v /In_find/In_dom /= Dx _ _ _ /dom_node2lay;
apply: leq_trans; [apply: Y|apply: Y1|apply: Y2].
Qed.

(* morphism-style properties *)

Lemma graph2lay0 {A} : graph2_lay (Unit : binary_graph A) = Unit.
Proof. by rewrite /graph2_lay assocs0 big_nil. Qed.

Lemma graph2lay_undef {A} : graph2_lay (undef : binary_graph A) = undef.
Proof. by []. Qed.

Lemma graph2layPt {A} x (v : A * (node * node)) :
        graph2_lay (pts x v) = node2_lay x v.
Proof.
rewrite /graph2_lay/node2_lay assocsPt validPt /=.
case: (x =P 0)=>[->|_] /=; first by rewrite pts_condN.
by rewrite big_cons big_nil unitR.
Qed.

Lemma graph2layUn {A} (g1 g2 : binary_graph A) :
        graph2_lay (g1 \+ g2) = graph2_lay g1 \+ graph2_lay g2.
Proof.
case: (normalP (g1 \+ g2))=>[E|V]; last first.
- rewrite /graph2_lay !big_assocs_dom !(validX V) /=.
  rewrite (perm_big _ (perm_domUn V)) big_cat /=.
  by congr (_ \+ _); apply: eq_Bigr=>x /mem_seqP Dx _;
  [rewrite findUnL ?Dx|rewrite findUnR ?Dx].
rewrite E graph2lay_undef /graph2_lay.
case: ifP=>Vg1; last by rewrite undef_join.
case: ifP=>Vg2; last by rewrite join_undef.
set h1 := (X in X \+ _); set h2 := (X in _ \+ X).
case: (normalP (h1 \+ h2))=>//; case: validUn=>// Vh1 Vh2 Dh _.
have V1 : valid (graph2_lay g1) by rewrite /graph2_lay Vg1 Vh1.
have V2 : valid (graph2_lay g2) by rewrite /graph2_lay Vg2 Vh2.
have : ~~ valid (g1 \+ g2) by rewrite E.
rewrite validUnAE Vg1 Vg2 /=.
case/allPn=>x Dx2 /=; rewrite negbK=>Dx1.
move: (graph2lay_sub V1 Dx1) (graph2lay_sub V2 Dx2).
rewrite /graph2_lay Vg1 Vg2=>Dh1 Dh2.
by move: (Dh x Dh1); rewrite Dh2.
Qed.

Lemma graph2layPtUn {A} x (v : A * (node * node)) (g : binary_graph A) :
        graph2_lay (pts x v \+ g) = node2_lay x v \+ graph2_lay g.
Proof. by rewrite graph2layUn graph2layPt. Qed.

(* graph2lay isn't a PCM morphism formally *)
(* because it doesn't preserve validity *)
(* as valid inputs can map to invalid outputs *)
Lemma graph2lay_is_pcm_morphism A : pcm_morph_axiom relT (@graph2_lay A).
Proof.
split=>[|x y V _]; first by rewrite /graph2_lay assocs0 big_nil.
rewrite -graph2layUn //; split=>//.
Abort.

(* spatial predicate definition and properties *)

Definition node2 {A} x (v : A * (node * node)) : Pred heap :=
  eq^~ (node2_lay x v).
Definition graph2 {A} (g : binary_graph A) : Pred heap :=
  eq^~ (graph2_lay g).

(* the layout determines the graph *)
(* proof uses dom_graph2lay and um_indf *)
(* to set up induction that depends on node ordering *)
Lemma graph2K {A} (g1 g2 : binary_graph A) h :
        valid h ->
        h \In graph2 g1 ->
        h \In graph2 g2 ->
        g1 = g2.
Proof.
move/[swap]=>-> V1; rewrite /graph2=>E.
have V2 : valid (graph2_lay g2) by rewrite -E.
move: (graph2layVI V1) (graph2layVI V2)=>Vg1 Vg2.
have : dom (graph2_lay g1) = dom (graph2_lay g2) by rewrite E.
rewrite !dom_graph2lay //; elim/um_indf: g1 g2 E Vg1 V1 Vg2 V2=>
[||x xs g1 IH V /(order_path_min trans) Ag] g2 E Vg1 V1 Vg2 V2.
- by rewrite big_nil; elim/um_indf: g2 E Vg2 V2.
- rewrite big_nil; elim/um_indf: g2 {E} Vg2 V2=>
  [||y ys g2 _ V /(order_path_min trans) Ag2] // Vg2 V2.
  by rewrite domPtUnK //= big_cons.
rewrite domPtUnK //= big_cons; elim/um_indf: g2 E V2 Vg2=>
[||y ys g2 IH2 W /(order_path_min trans) Ag2] E V2 Vg2.
- by rewrite big_nil.
- by rewrite big_nil.
rewrite domPtUnK // big_cons; case=>? _ _; subst y.
rewrite !graph2layPtUn // -!joinA in V1 V2 E.
case/(hcancelV V1): E=>E1 {}V1 /(hcancelV V1) [E2 {}V1].
case/(hcancelV V1)=>E3 {}V1 E /IH -> //.
- by rewrite (validR Vg1).
- by rewrite (validR Vg2).
- by rewrite (validX V2).
by rewrite (prod_eta xs) (prod_eta xs.2) E1 E2 E3 -!prod_eta.
Qed.

Lemma graph20 {A} : graph2 (Unit : binary_graph A) <~> emp.
Proof. by rewrite /graph2 graph2lay0. Qed.

Lemma graph2_undef {A} :
        graph2 (undef : binary_graph A) <~> eq^~ undef.
Proof. by rewrite /graph2 graph2lay_undef. Qed.

Lemma graph2Pt {A} x (v : A * (node * node)) :
        graph2 (pts x v) <~> node2 x v.
Proof. by rewrite /graph2 graph2layPt. Qed.

Lemma graph2Un {A} (g1 g2 : binary_graph A) :
        graph2 (g1 \+ g2) <~> graph2 g1 # graph2 g2.
Proof.
move=>h; split=>[->|[h1][h2][->{h}] ->->]; last by rewrite -graph2layUn.
by exists (graph2_lay g1), (graph2_lay g2); rewrite graph2layUn.
Qed.

Lemma graph2PtUn {A} x v (g : binary_graph A) :
        graph2 (pts x v \+ g) <~> node2 x v # graph2 g.
Proof. by rewrite graph2Un graph2Pt. Qed.

Lemma In_graph2_eta {A} (g : binary_graph A) x (v : A * (node * node)) :
        (x, v) \In g ->
        graph2 g <~> node2 x v # graph2 (free g x).
Proof. by move/In_eta=>E; rewrite {1}E graph2PtUn. Qed.

Lemma In_graph2V {A} (g : binary_graph A) h :
        h \In graph2 g ->
        valid h ->
        valid g.
Proof. by move=>->/graph2layVI. Qed.

Lemma In_graph2V2 {A} (g1 g2 : binary_graph A) h1 h2 :
        h1 \In graph2 g1 ->
        h2 \In graph2 g2 ->
        valid (h1 \+ h2) ->
        valid (g1 \+ g2).
Proof.
by move=>H1 H2 /In_graph2V; apply; rewrite graph2Un; exists h1, h2.
Qed.

