From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype ssrnat seq path.
(* temp*)
From mathcomp Require Import bigop.
From fcsl Require Import options axioms pred prelude seqperm.

From fcsl Require Import pcm unionmap heap autopcm automap.

Section All.
Variables (T : eqType).

Lemma subset_all a (s1 s2 : seq T) : {subset s1 <= s2} -> all a s2 -> all a s1.
Proof.
by move=>Hs /allP Ha1; apply/allP=>s /Hs /Ha1.
Qed.

End All.

Section FindLast.

Variables (T : Type).
Implicit Types (x : T) (p : pred T) (s : seq T).

Definition find_last p s :=
  let i := seq.find p (rev s) in
  if i == size s then size s else (size s - i).-1.

Lemma find_last_size p s : find_last p s <= size s.
Proof.
rewrite /find_last; case: ifP=>// _.
by rewrite -subnS; apply: leq_subr.
Qed.

Lemma has_find_last p s : has p s = (find_last p s < size s).
Proof.
rewrite /find_last -has_rev has_find -(size_rev s); case: ltngtP=>/=.
- move=>H; case/posnP: (size (rev s))=>[/eqP/nilP|] E.
  - by rewrite E /= in H.
  by rewrite -subnS ltn_subrL E.
- by rewrite ltnNge find_size.
by rewrite ltnn.
Qed.

Lemma nth_find_last x0 p s : has p s -> p (nth x0 s (find_last p s)).
Proof.
rewrite /find_last -has_rev -(size_rev s) => /[dup] E.
rewrite has_find ltn_neqAle; case/andP=>/negbTE H _; rewrite H.
move/(@nth_find _ x0): E; rewrite nth_rev; first by rewrite subnS size_rev.
by move: (find_size p (rev s)); rewrite leq_eqVlt H -(size_rev s).
Qed.

Lemma has_drop p s i : has p s -> has p (drop i.+1 s) = (i < find_last p s).
Proof.
rewrite /find_last -has_rev -(size_rev s) => /[dup] E.
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

Section UM.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map_class C V).

Lemma umfilt_predC (f : U) (p : pred (K * V)): f = um_filter p f \+ um_filter (predC p) f.
Proof.
rewrite -umfilt_dpredU; last by move=>? /=; rewrite negbK.
rewrite -[LHS]umfilt_predT; apply: eq_in_umfiltE=>kv /=.
by rewrite orbN.
Qed.

End UM.

Section UMEq.
Variables (K : ordType) (C : pred K) (V : eqType) (U : union_map_class C V).

Lemma rangeF k (f : U) : {subset range (free f k) <= range f}.
Proof.
case W: (valid f); last first.
- by move/negbT/invalidE: W=>->; rewrite free_undef !range_undef.
case D: (k \in dom f); last by move/negbT/dom_free: D=>->.
case: (um_eta D) W=>x [_] {1 3}-> Vf p.
by rewrite rangePtUn inE Vf=>->; rewrite orbT.
Qed.

(*
Lemma umpreim_cond (p : pred V) f k : um_preim (C:=C) (U:=U) p f k -> C k.
Proof.
rewrite /um_preim; case E: (find k f)=>[v|] //= _.
by move/find_some/dom_cond: E.
Qed.

Lemma umpreimPt (p : pred V) k v : C k -> um_preim (C:=C) (U:=U) p (pts k v) =1 [pred x | (x == k) && p v].
Proof.
move=>Hk x; rewrite /um_preim /= findPt2.
by case: eqP=>//= _; rewrite Hk.
Qed.
*)
End UMEq.

Section Sep.
Variable U : pcm.

Lemma sepitF {A} s (f1 f2 : A -> Pred U) :
        (forall x, x \In s -> f1 x =p f2 x) -> IterStar.sepit s f1 =p IterStar.sepit s f2.
Proof.
elim: s=>[|x s IH] H h; first by rewrite !IterStar.sepit0.
have /IH {IH}H': forall x : A, x \In s -> f1 x =p f2 x.
  by move=>? H0; apply: H; apply/In_cons; right.
have Hx : x \In x :: s by apply/In_cons; left.
by rewrite !IterStar.sepit_cons; split; case=>h1[h2][{h}-> H1 H2]; exists h1, h2;
split=>//; [rewrite -H | rewrite -H' | rewrite H | rewrite H'].
Qed.

Lemma sepit_perm {A} s1 s2 (f : A -> Pred U) :
        perm s1 s2 -> IterStar.sepit s1 f =p IterStar.sepit s2 f.
Proof.
elim: s1 s2 =>[|x s1 IH] s2 /=; first by move/pperm_nil=>->.
move=>H.
have Hx: x \In s2 by apply/(pperm_in H)/In_cons; left.
case: (In_split Hx)=>s21[s22] E; rewrite {s2 Hx}E in H *.
move/pperm_cons_cat_cons: H=>H.
rewrite IterStar.sepit_cons IterStar.sepit_cat /= =>h0; split.
- case=>h1[h2][{h0}-> H1]; rewrite (IH _ H) IterStar.sepit_cat.
  case=>_[_][{h2}-> [hs3][E3 -> H3] [hs4][E4 -> H4]]; rewrite joinCA.
  exists (IterStar.bigjoin hs3), (h1 \+ IterStar.bigjoin hs4); split=>//; first by exists hs3.
  by rewrite IterStar.sepit_cons; exists h1, (IterStar.bigjoin hs4); split=>//; exists hs4.
case=>_[h2][{h0}-> [hs1][Hs1 -> H1]]; rewrite IterStar.sepit_cons.
case=>h3[_][{h2}-> H3 [hs2][Hs2 -> H2]]; rewrite joinCA.
exists h3, (IterStar.bigjoin hs1 \+ IterStar.bigjoin hs2); split=>//.
rewrite (IH _ H); exists (hs1 ++ hs2); split.
- by rewrite !size_cat Hs1 Hs2.
- by rewrite /IterStar.bigjoin big_cat.
by rewrite /IterStar.bigand zip_cat //; apply/IterStar.bigand_cat.
Qed.

End Sep.

(* pointer map, a generic finite map keyed by non-null pointers *)
Notation ptr_pred := (fun x : ptr => x != null).

Module Type PMSig.

Parameter tp : Type -> Type.

Section Params.
Variable A : Type.
Notation tp := (tp A).

Parameter pg_undef : tp.
Parameter defined : tp -> bool.
Parameter empty : tp.
Parameter upd : ptr -> A -> tp -> tp.
Parameter dom : tp -> seq ptr.
Parameter dom_eq : tp -> tp -> bool.
Parameter assocs : tp -> seq (ptr * A).
Parameter free : tp -> ptr -> tp.
Parameter find : ptr -> tp -> option A.
Parameter union : tp -> tp -> tp.
Parameter empb : tp -> bool.
Parameter undefb : tp -> bool.
Parameter pts : ptr -> A -> tp.

Parameter from : tp -> @UM.base ptr_ordType ptr_pred A.
Parameter to : @UM.base ptr_ordType ptr_pred A -> tp.

Axiom ftE : forall b, from (to b) = b.
Axiom tfE : forall f, to (from f) = f.
Axiom undefE : pg_undef = to (@UM.Undef ptr_ordType ptr_pred A).
Axiom defE : forall f, defined f = UM.valid (from f).
Axiom emptyE : empty = to (@UM.empty ptr_ordType ptr_pred A).
Axiom updE : forall k v f, upd k v f = to (UM.upd k v (from f)).
Axiom domE : forall f, dom f = UM.dom (from f).
Axiom dom_eqE : forall f1 f2, dom_eq f1 f2 = UM.dom_eq (from f1) (from f2).
Axiom assocsE : forall f, assocs f = UM.assocs (from f).
Axiom freeE : forall f k, free f k = to (UM.free (from f) k).
Axiom findE : forall k f, find k f = UM.find k (from f).
Axiom unionE : forall f1 f2, union f1 f2 = to (UM.union (from f1) (from f2)).
Axiom empbE : forall f, empb f = UM.empb (from f).
Axiom undefbE : forall f, undefb f = UM.undefb (from f).
Axiom ptsE : forall k v, pts k v = to (@UM.pts ptr_ordType ptr_pred A k v).

End Params.
End PMSig.

Module PMDef : PMSig.
Section PMDef.
Variable A : Type.

Definition tp : Type := @UM.base ptr_ordType ptr_pred A.

Definition pg_undef := @UM.Undef ptr_ordType ptr_pred A.
Definition defined f := @UM.valid ptr_ordType ptr_pred A f.
Definition empty := @UM.empty ptr_ordType ptr_pred A.
Definition upd k v f := @UM.upd ptr_ordType ptr_pred A k v f.
Definition dom f := @UM.dom ptr_ordType ptr_pred A f.
Definition dom_eq f1 f2 := @UM.dom_eq ptr_ordType ptr_pred A f1 f2.
Definition assocs f := @UM.assocs ptr_ordType ptr_pred A f.
Definition free f k := @UM.free ptr_ordType ptr_pred A f k.
Definition find k f := @UM.find ptr_ordType ptr_pred A k f.
Definition union f1 f2 := @UM.union ptr_ordType ptr_pred A f1 f2.
Definition empb f := @UM.empb ptr_ordType ptr_pred A f.
Definition undefb f := @UM.undefb ptr_ordType ptr_pred A f.
Definition pts k v := @UM.pts ptr_ordType ptr_pred A k v.

Definition from (f : tp) : @UM.base ptr_ordType ptr_pred A := f.
Definition to (b : @UM.base ptr_ordType ptr_pred A) : tp := b.

Lemma ftE b : from (to b) = b. Proof. by []. Qed.
Lemma tfE f : to (from f) = f. Proof. by []. Qed.
Lemma undefE : pg_undef = to (@UM.Undef ptr_ordType ptr_pred A). Proof. by []. Qed.
Lemma defE f : defined f = UM.valid (from f). Proof. by []. Qed.
Lemma emptyE : empty = to (@UM.empty ptr_ordType ptr_pred A). Proof. by []. Qed.
Lemma updE k v f : upd k v f = to (UM.upd k v (from f)). Proof. by []. Qed.
Lemma domE f : dom f = UM.dom (from f). Proof. by []. Qed.
Lemma dom_eqE f1 f2 : dom_eq f1 f2 = UM.dom_eq (from f1) (from f2).
Proof. by []. Qed.
Lemma assocsE f : assocs f = UM.assocs (from f). Proof. by []. Qed.
Lemma freeE f k : free f k = to (UM.free (from f) k). Proof. by []. Qed.
Lemma findE k f : find k f = UM.find k (from f). Proof. by []. Qed.
Lemma unionE f1 f2 : union f1 f2 = to (UM.union (from f1) (from f2)).
Proof. by []. Qed.
Lemma empbE f : empb f = UM.empb (from f). Proof. by []. Qed.
Lemma undefbE f : undefb f = UM.undefb (from f). Proof. by []. Qed.
Lemma ptsE k v : pts k v = to (@UM.pts ptr_ordType ptr_pred A k v).
Proof. by []. Qed.

End PMDef.
End PMDef.

Notation ptrmap := PMDef.tp.

Definition ptrmapMixin A :=
  UMCMixin (@PMDef.ftE A) (@PMDef.tfE A) (@PMDef.defE A)
           (@PMDef.undefE A) (@PMDef.emptyE A) (@PMDef.updE A)
           (@PMDef.domE A) (@PMDef.dom_eqE A) (@PMDef.assocsE A)
           (@PMDef.freeE A) (@PMDef.findE A) (@PMDef.unionE A)
           (@PMDef.empbE A) (@PMDef.undefbE A) (@PMDef.ptsE A).

Canonical ptrmapUMC A :=
  Eval hnf in UMC (ptrmap A) (@ptrmapMixin A).

(* we add the canonical projections matching against naked type *)
(* thus, there are two ways to get a PCM for a union map: *)
(* generic one going through union_map_classPCM, and another by going *)
(* through union_mapPCM. Luckily, they produce equal results *)
(* and this is just a matter of convenience *)
(* Ditto for the equality type *)

Definition ptrmapPCMMix A := union_map_classPCMMix (ptrmapUMC A).
Canonical ptrmapPCM A := Eval hnf in PCM (ptrmap A) (@ptrmapPCMMix A).

Definition ptrmapCPCMMix A := union_map_classCPCMMix (ptrmapUMC A).
Canonical ptrmapCPCM A := Eval hnf in CPCM (ptrmap A) (@ptrmapCPCMMix A).

Definition ptrmapTPCMMix A := union_map_classTPCMMix (ptrmapUMC A).
Canonical ptrmapTPCM A := Eval hnf in TPCM (ptrmap A) (@ptrmapTPCMMix A).

Definition ptrmap_eqMix (A : eqType) :=
  @union_map_class_eqMix ptr_ordType ptr_pred A _ (@ptrmapMixin A).
Canonical ptrmap_eqType (A : eqType) :=
  Eval hnf in EqType (ptrmap A) (@ptrmap_eqMix A).

(* installing the Pred structure for writing x \In h *)
Canonical Structure ptrmap_PredType A : PredType (ptr * A) :=
  Mem_UmMap_PredType (ptrmapUMC A).
Coercion Pred_of_ptrmap A (f : ptrmap A) : Pred_Class := [eta Mem_UmMap f].

Definition pg_pts A (k : ptr) (v : A) :=
  @UMC.pts ptr_ordType ptr_pred A (ptrmapUMC A) k v.

(* baking ptr_pred into the notation *)
Notation "x &-> v" := (@pg_pts _ x v) (at level 30).

Fact no_null A (g : ptrmap A) :
  null \notin dom g.
Proof. by apply/negP=>/dom_cond. Qed.

(* pregraph is a pointer map to `seq ptr`, a form of adjacency list *)
(* technically it's a "prequiver", because it allows loops and parallel edges *)
Definition pregraph := [pcm of ptrmap (seq ptr)].

(* a finite set of nodes (can have nulls) *)
Definition nodeset := [pcm of fset [ordType of ptr]].

(* graph ops and properties *)
Section GraphOps.

(* TODO `(p != null) ==> p \in dom g` ? *)
Definition good_ptr (g : pregraph) p : bool := (p == null) || (p \in dom g).

Definition good_graph (g : pregraph) : bool :=
  valid g &&
  all (all (good_ptr g)) (range g).

(* p has no incoming connections *)
Definition out_node (g : pregraph) p : bool := all (fun s => p \notin s) (range g).

Lemma good_graphF g p :
  out_node g p ->
  good_graph g ->
  good_graph (free g p).
Proof.
move=>Hna; rewrite /good_graph /out_node.
case/andP=>Va Ha; rewrite validF Va /=.
apply/allP=>s /rangeF Hs.
move/allP: Hna=>/(_ _ Hs) Hp.
move/allP: Ha=>/(_ _ Hs) /allP {}Hs.
apply/allP=>q Hq; move: (Hs _ Hq).
rewrite /good_ptr; case/orP=>[->|] // Hqd.
apply/orP; right; rewrite domF inE Hqd.
by case: eqP=>// E; rewrite E Hq in Hp.
Qed.

Definition links (g : pregraph) (x : ptr) : option (seq ptr) :=
  ssrfun.omap (filter (fun x => x \in dom g)) (find x g).

  (*
Lemma linksPtUn g p ns x :
  valid (p &-> ns \+ g) ->
  links (p &-> ns \+ g) x = if x == p
                             then Some (filter (fun x => (p == x) || (x \in dom g)) ns)
                             else ssrfun.omap (fun xs => filter (fun x => p == x) ns ++ xs) (links g x).
Proof.
move=>V.
rewrite /links findPtUn2 //; case: eqP=>/=.
- by move=>{x}_; congr Some; apply: eq_filter=>z; rewrite domPtUn V inE.
move=>H; case E: (find x g)=>[v|]//=; congr Some.
rewrite -filter_cat.
rewrite -filter_predI; apply: eq_in_filter=>z Hz /=; rewrite domPtUn V inE /=.
  - rewrite domPtUn.
  Unset Printing Notations.
*)
Definition edge (g : pregraph) x y :=
  oapp (fun ys => y \in ys) false (links g x).

(*
Lemma edgePtUn g p ns x y :
  valid (p &-> ns \+ g) ->
  edge (p &-> ns \+ g) x y = (x == p) || edge g x y.
Proof.
move=>V.
rewrite /edge /links findPtUn2 //.
case: eqP=>/=.
*)
Arguments edge g x y : simpl never.

Lemma edgeUn g0 g x y :
  valid (g0 \+ g) ->
  edge g x y -> edge (g0 \+ g) x y.
Proof.
move=>V; rewrite /edge /links findUnR //.
case: dom_find=>[|v] -> //= Hg.
rewrite !mem_filter domUn inE.
by case/andP=>->->; rewrite orbT !andbT.
Qed.

Fixpoint dfs (p : nodeset) (g : pregraph) n (v : seq ptr) x :=
  if x \in [predU v & (dom p)] then v else
  if links g x is Some xs then
  if n is n'.+1 then foldl (dfs p g n') (x :: v) xs else v
  else v.

(* TODO links+dom+edge spec lemma? *)
Lemma linksF g x :
  links g x = None <-> x \notin dom g.
Proof. by rewrite /links; case: (dom_find x)=>[|v] ->. Qed.

Lemma linksT g x xs : links g x = Some xs ->
                        (x \in dom g) * (all (fun z => z \in dom g) xs).
Proof.
rewrite /links; case Hf: (find x g)=>[ns|] //=.
case=><-; split; first by move/find_some: Hf.
rewrite -/(filter (fun x => x \in dom g) ns) all_filter.
by apply/sub_all/all_predT=>z _ /=; apply: implybb.
Qed.

Corollary edge_dom g x y : edge g x y -> (x \in dom g) * (y \in dom g).
Proof.
rewrite /edge; case E: (links g x)=>[v|]//= Ey.
case/linksT: E=>E1 E2; split=>//.
by move/allP: E2; apply.
Qed.

Lemma find_edge g x ns y :
  find x g = Some ns ->
  edge g x y = (y \in dom g) && (y \in ns).
Proof.
move=>E; rewrite /edge /links E [filter _]lock /=.
by unlock; rewrite mem_filter.
Qed.

Lemma links_edge g x xs y : links g x = Some xs -> edge g x y = (y \in xs).
Proof. by move=>E; rewrite /edge E. Qed.

Lemma links_edge_not g x y : links g x = None -> ~~ edge g x y.
Proof. by move=>E; rewrite /edge E. Qed.

Lemma subset_dfs p g n v a : {subset v <= foldl (dfs p g n) v a}.
Proof.
elim: n a v => [|n IHn].
- elim=>/= [|h t IH] v; first by move=>?.
  by case: ifP=>//; case: (links g h).
elim=>/=[|h t IHa v]; first by move=>?.
move=>x Hx; apply: IHa; case: ifP=>// _; case: (links g h)=>// xs.
by apply: IHn; rewrite inE Hx orbT.
Qed.

Lemma subset_foldl_dfs_dom p g n v x :
  {subset v <= dom g} ->
  {subset foldl (dfs p g n) v x <= dom g}.
Proof.
elim: n x v=>/=[|n IH]; elim=>//= h t IHx v Hv; case: ifP=>_; try by [apply: IHx];
case Ep: (links g h)=>[ls|]/=; apply: IHx=>{t}//.
apply: IH=>z; rewrite inE; case/orP; last by apply: Hv.
by move/eqP=>{z}->; rewrite (linksT Ep).
Qed.

Corollary subset_dfs_dom p g n v x :
  {subset v <= dom g} ->
  {subset dfs p g n v x <= dom g}.
Proof.
case: n=>/= [|n] H; first by case: ifP=>// _; case: (links g x).
move=>z; case: ifP=>_; first by move/H.
case Ep: (links g x)=>[ls|] /=; last by move/H.
apply: subset_foldl_dfs_dom=>{}z; rewrite inE; case/orP; last by apply/H.
by move/eqP=>{z}->; rewrite (linksT Ep).
Qed.

Lemma uniq_dfs_foldl p g n v x : uniq v -> uniq (foldl (dfs p g n) v x).
Proof.
elim: n x v=>/=[|n IH]; elim=>//= h t IHx v Hv; case: ifP=>Hh; try by [apply: IHx];
case: (links g h)=>[ls|]/=; apply: IHx=>{t}//.
move/negbT: Hh; rewrite negb_or; case/andP=>Hh _.
by apply/IH=>/=; rewrite Hv andbT.
Qed.

Corollary uniq_dfs p g n v x :
  uniq v ->
  uniq (dfs p g n v x).
Proof.
case: n=>/= [|n] H; case: ifP=>// Hx; case: (links g x)=>// xs.
move/negbT: Hx; rewrite negb_or; case/andP=>Hx _.
by apply: uniq_dfs_foldl=>/=; rewrite H andbT.
Qed.

Variant dfs_path (p : nodeset) g (v : seq ptr) x y : Prop :=
  DfsPath xs of
    path (edge g) x xs &
    y = last x xs &
    nilp xs ==> (x \in dom g) &
    all (fun z => z \notin [predU v & (dom p)]) (x::xs).

Lemma dfs_path_id p g v x :
  x \in dom g ->
  x \notin dom p -> x \notin v -> dfs_path p g v x x.
Proof.
move=>Hx Nx Nv; apply (DfsPath (xs:=[::]))=>//=.
by rewrite andbT inE negb_or Nv.
Qed.

Lemma path_dom g x xs :
  path (edge g) x xs ->
  all (fun z => z \in dom g) xs.
Proof.
elim: xs x=>//=a xs IH x; case/andP=>He Hp.
by apply/andP; split; [case/edge_dom: He | apply: (IH _ Hp)].
Qed.

Lemma dfs_pathP p g n x y v :
  size (dom g) <= size v + n ->
  uniq v ->
  {subset v <= dom g} ->
  y \notin v ->
  reflect (dfs_path p g v x y) (y \in dfs p g n v x).
Proof.
elim: n => [|n IHn] /= in x y v * => Hv Uv Sv Ny.
- rewrite addn0 in Hv.
  case: (uniq_min_size Uv Sv Hv) Ny=>_ /(_ y) Ey.
  move/negbTE=>Ny; rewrite Ey in Ny.
  suff: ~dfs_path p g v x y by case: (links g x)=>[_|]; rewrite if_same Ey Ny; apply: ReflectF.
  case; case; first by move=>/= _ <-; rewrite Ny.
  by move=>a l /path_dom/allP /(_ y) + /= Eyl; rewrite Ny Eyl mem_last; move/[apply].
case Epl: (links g x)=>[ls|] /=; last first.
- rewrite if_same (negbTE Ny); apply: ReflectF; case=>/= xs.
  case: xs=>[|??]/=; last by rewrite (negbTE (links_edge_not _ Epl)).
  by move=>_ Ey Hy; move/linksF/negbTE: Epl; rewrite Hy.
have [Vx|] := ifPn.
- rewrite (negbTE Ny); apply: ReflectF; case=>/= xs.
  by rewrite Vx.
rewrite negb_or; case/andP=>Nx Px.
set v1 := x :: v; have [-> | Nyx] := eqVneq y x.
- rewrite subset_dfs; last by rewrite inE eq_refl.
  apply: ReflectT; apply: dfs_path_id=>//.
  by case/linksT: Epl.
apply: (@equivP (exists2 x1, x1 \in ls & dfs_path p g v1 x1 y)); last first.
- split=> {IHn} [[x1 Hx1 [p1 P1 Ey Py]] | [p1 /shortenP []]] /=.
  - case/andP; rewrite !inE !negb_or -andbA; case/and3P=>Ex1 Ex1v Nx1 Ha1; apply: (DfsPath (xs:=x1::p1))=>//=.
    - by rewrite P1 andbT (links_edge _ Epl).
    rewrite !inE !negb_or Nx Px Ex1v Nx1 /=.
    by apply/sub_all/Ha1=>z; rewrite !inE !negb_or -andbA; case/and3P=>_->->.
  case=>[_ _ _ /= Eyx | x1 xs /=]; first by case/eqP: Nyx.
  rewrite (links_edge _ Epl) /=; case/andP=>Hx1 Hp1 /and3P [H11 H12 H13] H2 H3 H4 /andP [H5 H6].
  exists x1=>//; apply: (DfsPath (xs:=xs))=>//.
  - by apply/implyP=>_; case/linksT: Epl=>_ /allP /(_ _ Hx1).
  apply/allP=>z /[dup] Hz /H2; move/allP: H6=>/(_ z) /[apply].
  rewrite !inE !negb_or; case/andP=>->->/=; rewrite !andbT; apply/negP=>/eqP Ez.
  by rewrite -Ez Hz in H11.
have{Nyx Ny}: y \notin v1 by apply/norP.
have{Nx Uv}: uniq v1 by rewrite /= Nx.
have{Sv}: {subset v1 <= dom g}.
- move=>z; rewrite inE; case/orP; last by move/Sv.
  by move/eqP=>{z}->; case/linksT: Epl.
have{Hv}: size (dom g) <= size v1 + n by rewrite addSnnS.
case/linksT: Epl=>_ Hl.
elim: {x Px v}ls Hl v1 => /= [_|x a IHa /andP [Ha Hl]] v /= Hv Sv Uv Nv.
- by rewrite (negPf Nv); apply: ReflectF; case.
set v2 := dfs p g n v x; have v2v: {subset v <= v2} := @subset_dfs p g n v [:: x].
have [Hy2 | Ny2] := boolP (y \in v2).
- rewrite subset_dfs //; apply: ReflectT; exists x; first by rewrite inE eq_refl.
  by apply/IHn.
apply: {IHa}(equivP (IHa Hl _ _ _ _ Ny2)).
- by apply: (leq_trans Hv); rewrite leq_add2r; apply: uniq_leq_size.
- by apply: subset_dfs_dom.
- by apply: uniq_dfs.
split=> [] [x1 Hx1 [p1 P1 Ey Py Nay]].
  exists x1; first by rewrite inE Hx1 orbT.
  apply: (DfsPath (xs:=p1))=>//; apply/sub_all/Nay=>z; apply: contra.
  by rewrite !inE; case/orP; [move/v2v=>->|move=>->; rewrite orbT].
suff Nv2: all (fun z => z \notin v2) (x1 :: p1).
- move: Hx1; rewrite inE; case/orP=>[/eqP Ex1|Hx1]; last first.
  - exists x1=>//; apply: (DfsPath (xs:=p1))=>//.
    apply/allP=>z Hz; rewrite inE negb_or; apply/andP; split.
    - by move/allP: Nv2; apply.
    by move/allP: Nay=>/(_ _ Hz); rewrite inE negb_or; case/andP.
  rewrite {x1}Ex1 in P1 Py Ey Nay Nv2.
  exfalso; move: Nv2=>/=; case/andP=>+ _; move/negbTE/negP; apply.
  suff [Nx Nxp]: (x \notin v) /\ (x \notin dom p).
  - by apply/IHn=>//; apply: dfs_path_id.
  by move: Nay=>/=; case/andP; rewrite inE negb_or; case/andP.
apply: contraR Ny2; case/allPn => x2 Hx2 /negbNE Hx2v.
case/splitPl: Hx2 Ey P1 Nay => p0 p2 p0x2.
rewrite last_cat cat_path -cat_cons lastI cat_rcons {}p0x2 => p2y /andP[_ g_p2].
rewrite all_cat /=; case/and3P=> {p0}_; rewrite inE negb_or; case/andP=>Nx2v Nx2p Np2.
have{Nx2v Hx2v} [p3 g_p1 p1_x2 V2 not_p1v] := (IHn _ _ v Hv Uv Sv Nx2v Hx2v).
apply/IHn=>//; exists (p3 ++ p2)=>//.
- by rewrite cat_path g_p1 -p1_x2.
- by rewrite last_cat -p1_x2.
- by rewrite cat_nilp; apply/implyP; case/andP=>+ _; apply/implyP.
by rewrite -cat_cons all_cat not_p1v.
Qed.

Definition component p g x : seq ptr := dfs p g (size (dom g)) [::] x.

Definition connect p g : rel ptr := [rel x y | y \in component p g x].
Canonical connect_app_pred p g x := ApplicativePred (connect p g x).

Corollary connectP p g x y :
  reflect (exists xs, [/\ path (edge g) x xs,
                          y = last x xs,
                          nilp xs ==> (x \in dom g) &
                          all (fun z => z \notin (dom p)) (x::xs)])
          (connect p g x y).
Proof.
apply: (iffP (dfs_pathP _ _ _ _ _ _))=>//.
- by case=>xs P Ey Pv Ha; exists xs.
by case=>xs [P Ey Pv Ha]; apply: (DfsPath (xs:=xs)).
Qed.

Lemma connect_trans p g : transitive (connect p g).
Proof.
move=> x y z /connectP [xs][Hxs -> Hp Ha] /connectP [ys][Hys -> Hp' Ha']; apply/connectP.
exists (xs ++ ys); rewrite cat_path last_cat Hxs /=; split=>//.
- by rewrite cat_nilp; apply/implyP; case/andP=>+ _; apply/implyP.
rewrite all_cat andbA; apply/andP; split=>//.
by move: Ha'=>/=; case/andP.
Qed.

Lemma connect0 p g x : x \in dom g -> x \notin dom p -> connect p g x x.
Proof. by move=>Hd Hp; apply/connectP; exists [::]; rewrite /= andbT. Qed.

Lemma connectUn p g0 g x y :
  valid (g0 \+ g) ->
  connect p g x y -> connect p (g0 \+ g) x y.
Proof.
move=>V; case/connectP=>xs [Hp {y}-> /implyP Nxs Ha].
apply/connectP; exists xs; split=>//; last first.
- rewrite domUn inE; rewrite V /=.
  by apply/implyP=>/Nxs->; rewrite orbT.
elim: xs {Nxs Ha}x Hp=>//= y xs IH x; case/andP=>Hxy Hxs.
by apply/andP; split; [apply: edgeUn | apply: IH].
Qed.

Lemma connect_dom p g x y :
  y \in connect p g x -> (x \in dom g) * (y \in dom g).
Proof.
case/connectP; case=>[|h t]; case; first by move=>/= _ ->.
move/[dup]/path_dom=>Ha /=; case/andP=>/edge_dom [Hx _] _ Ey _ _; split=>//.
by apply: (allP Ha); rewrite Ey; exact: mem_last.
Qed.

Corollary connect_notd p g x : x \notin dom g -> connect p g x =i pred0.
Proof.
move=>Hx y; rewrite [RHS]inE; apply/negP; case/connect_dom=>E.
by rewrite E in Hx.
Qed.

Lemma connect_notp p g x : x \in dom p -> connect p g x =i pred0.
Proof.
move=>Hx y; rewrite [RHS]inE; apply/negbTE/connectP.
by case=>xs /= [_ _ _]; case/andP; rewrite Hx.
Qed.

Lemma connect_sub g p1 p2 x :
  {subset dom p2 <= dom p1} ->
  {subset connect p1 g x <= connect p2 g x}.
Proof.
move=>Hp z; case/connectP=>xs [Hxs {z}-> H Ha].
apply/connectP; exists xs; split=>//.
by apply/sub_all/Ha=>z; apply/contra/Hp.
Qed.

Lemma connect_links_sub p g x ns :
  find x g = Some ns ->
  forall y, y \in connect p g x -> (y == x) || has (fun n => y \in connect p g n) ns.
Proof.
move=>Hx y.
case/connectP=>xs [Hp {y}-> H].
case: xs Hp H=>[|h xs]/=; first by move=>_ _; rewrite eq_refl.
case/andP; rewrite (find_edge _ Hx); case/andP=>Hh Hns Hxs _; case/and3P=>Hxp Hcp Ha.
apply/orP; right; apply/hasP; exists h=>//.
by apply/connectP; exists xs; rewrite Hh /= Hcp Ha; split=>//; apply: implybT.
Qed.

Lemma connect_eq_links p g x ns :
  find x g = Some ns ->
  x \notin dom p ->
  forall y, y \in connect p g x = (y == x) || has (fun n => y \in connect p g n) ns.
Proof.
move=>Hx Hd y; apply/iffE; split; first by apply: connect_links_sub.
case/orP.
- move/eqP=>->; apply: connect0=>//.
  by move/find_some: Hx.
case/hasP=>n Hn.
case/connectP=>xs [Hp {y}-> H] /=; case/andP=>Hn1 Ha; apply/connectP.
exists (n::xs)=>/=; rewrite Hp Hd Hn1 Ha /= andbT; split=>//.
rewrite (find_edge _ Hx) Hn andbT.
by case: {Ha}xs Hp H=>//= ??; case/andP; case/edge_dom.
Qed.

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

Lemma connectMPtUn p m g x cs :
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

Lemma connectMUn p m1 m2 g x c cs :
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
case: {-1}_ _ _ / (split_find_last Hpxs) (erefl (x::xs))=>{Hpxs} q xs1 xs2 Hq.
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

Corollary connectMUnHas p m1 m2 g c cs :
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
  valid (g0 \+ g) ->
  symconnect p g x y -> symconnect p (g0 \+ g) x y.
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
  valid (g0 \+ g) ->
  preacyclic (g0 \+ g) -> preacyclic g.
Proof.
move=>V /allrelP H; apply/allrelP=>x y Hx Hy; apply/implyP=>Hs.
have Hx1: x \in dom (g0 \+ g) by rewrite domUn inE V Hx orbT.
have Hy1: y \in dom (g0 \+ g) by rewrite domUn inE V Hy orbT.
move/implyP: (H _ _ Hx1 Hy1); apply.
by apply: symconnectUn.
Qed.

Definition acyclic g := all (fun x => ~~ edge g x x) (dom g) && preacyclic g.

Lemma acyclicUn g0 g :
  valid (g0 \+ g) ->
  acyclic (g0 \+ g) -> acyclic g.
Proof.
move=>V; case/andP=>Ha Hp; apply/andP; split; last by apply: (preacyclicUn V Hp).
apply/allP=>x Hx.
suff: ~~ edge (g0 \+ g) x x by apply/contra/edgeUn.
by move/allP: Ha; apply; rewrite domUn inE V Hx orbT.
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