From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype ssrnat seq path.
From pcm Require Import options axioms pred prelude seqperm.

From pcm Require Import pcm unionmap heap autopcm automap.
From htt Require Import interlude model heapauto.
From htt Require Import graph.

(*
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

End UM.

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

Variant bin_node := BN of ptr & ptr.

Definition bn_get : bin_node -> ptr * ptr :=
  fun '(BN l r) => (l, r).

Definition bn_sub : ptr * ptr -> bin_node :=
  fun '(l, r) => BN l r.

Lemma bn_ccl : ssrfun.cancel bn_get bn_sub.
Proof. by case; case. Qed.

Definition binnode_eqMixin := CanEqMixin bn_ccl.
Canonical binnode_eqType := Eval hnf in EqType _ binnode_eqMixin.

(* pregraph as a union map `ptr :-> bin_node` *)

Notation ptr_pred := (fun x : ptr => x != null).

Module Type PGSig.

Parameter tp : Type.

Section Params.

Parameter pg_undef : tp.
Parameter defined : tp -> bool.
Parameter empty : tp.
Parameter upd : ptr -> bin_node -> tp -> tp.
Parameter dom : tp -> seq ptr.
Parameter dom_eq : tp -> tp -> bool.
Parameter assocs : tp -> seq (ptr * bin_node).
Parameter free : tp -> ptr -> tp.
Parameter find : ptr -> tp -> option bin_node.
Parameter union : tp -> tp -> tp.
Parameter empb : tp -> bool.
Parameter undefb : tp -> bool.
Parameter pts : ptr -> bin_node -> tp.

Parameter from : tp -> @UM.base ptr_ordType ptr_pred bin_node.
Parameter to : @UM.base ptr_ordType ptr_pred bin_node -> tp.

Axiom ftE : forall b, from (to b) = b.
Axiom tfE : forall f, to (from f) = f.
Axiom undefE : pg_undef = to (@UM.Undef ptr_ordType ptr_pred bin_node).
Axiom defE : forall f, defined f = UM.valid (from f).
Axiom emptyE : empty = to (@UM.empty ptr_ordType ptr_pred bin_node).
Axiom updE : forall k v f, upd k v f = to (UM.upd k v (from f)).
Axiom domE : forall f, dom f = UM.dom (from f).
Axiom dom_eqE : forall f1 f2, dom_eq f1 f2 = UM.dom_eq (from f1) (from f2).
Axiom assocsE : forall f, assocs f = UM.assocs (from f).
Axiom freeE : forall f k, free f k = to (UM.free (from f) k).
Axiom findE : forall k f, find k f = UM.find k (from f).
Axiom unionE : forall f1 f2, union f1 f2 = to (UM.union (from f1) (from f2)).
Axiom empbE : forall f, empb f = UM.empb (from f).
Axiom undefbE : forall f, undefb f = UM.undefb (from f).
Axiom ptsE : forall k v, pts k v = to (@UM.pts ptr_ordType ptr_pred bin_node k v).

End Params.
End PGSig.

Module PGDef : PGSig.
Section PGDef.

Definition tp : Type := @UM.base ptr_ordType ptr_pred bin_node.

Definition pg_undef := @UM.Undef ptr_ordType ptr_pred bin_node.
Definition defined f := @UM.valid ptr_ordType ptr_pred bin_node f.
Definition empty := @UM.empty ptr_ordType ptr_pred bin_node.
Definition upd k v f := @UM.upd ptr_ordType ptr_pred bin_node k v f.
Definition dom f := @UM.dom ptr_ordType ptr_pred bin_node f.
Definition dom_eq f1 f2 := @UM.dom_eq ptr_ordType ptr_pred bin_node f1 f2.
Definition assocs f := @UM.assocs ptr_ordType ptr_pred bin_node f.
Definition free f k := @UM.free ptr_ordType ptr_pred bin_node f k.
Definition find k f := @UM.find ptr_ordType ptr_pred bin_node k f.
Definition union f1 f2 := @UM.union ptr_ordType ptr_pred bin_node f1 f2.
Definition empb f := @UM.empb ptr_ordType ptr_pred bin_node f.
Definition undefb f := @UM.undefb ptr_ordType ptr_pred bin_node f.
Definition pts k v := @UM.pts ptr_ordType ptr_pred bin_node k v.

Definition from (f : tp) : @UM.base ptr_ordType ptr_pred bin_node := f.
Definition to (b : @UM.base ptr_ordType ptr_pred bin_node) : tp := b.

Lemma ftE b : from (to b) = b. Proof. by []. Qed.
Lemma tfE f : to (from f) = f. Proof. by []. Qed.
Lemma undefE : pg_undef = to (@UM.Undef ptr_ordType ptr_pred bin_node). Proof. by []. Qed.
Lemma defE f : defined f = UM.valid (from f). Proof. by []. Qed.
Lemma emptyE : empty = to (@UM.empty ptr_ordType ptr_pred bin_node). Proof. by []. Qed.
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
Lemma ptsE k v : pts k v = to (@UM.pts ptr_ordType ptr_pred bin_node k v).
Proof. by []. Qed.

End PGDef.
End PGDef.

Notation pregraph := PGDef.tp.

Definition pregraphMixin :=
  UMCMixin PGDef.ftE PGDef.tfE PGDef.defE
           PGDef.undefE PGDef.emptyE PGDef.updE
           PGDef.domE PGDef.dom_eqE PGDef.assocsE
           PGDef.freeE PGDef.findE PGDef.unionE
           PGDef.empbE PGDef.undefbE PGDef.ptsE.

Canonical pregraphUMC :=
  Eval hnf in UMC pregraph pregraphMixin.

(* we add the canonical projections matching against naked type *)
(* thus, there are two ways to get a PCM for a union map: *)
(* generic one going through union_map_classPCM, and another by going *)
(* through union_mapPCM. Luckily, they produce equal results *)
(* and this is just a matter of convenience *)
(* Ditto for the equality type *)

Definition pregraphPCMMix := union_map_classPCMMix pregraphUMC.
Canonical pregraphPCM := Eval hnf in PCM pregraph pregraphPCMMix.

Definition pregraphCPCMMix := union_map_classCPCMMix pregraphUMC.
Canonical pregraphCPCM := Eval hnf in CPCM pregraph pregraphCPCMMix.

Definition pregraphTPCMMix := union_map_classTPCMMix pregraphUMC.
Canonical pregraphTPCM := Eval hnf in TPCM pregraph pregraphTPCMMix.

Definition pregraph_eqMix :=
  @union_map_class_eqMix ptr_ordType ptr_pred binnode_eqType _ pregraphMixin.
Canonical pregraph_eqType :=
  Eval hnf in EqType pregraph pregraph_eqMix.

(* installing the Pred structure for writing x \In h *)
Canonical Structure pregraph_PredType : PredType (ptr * bin_node) :=
  Mem_UmMap_PredType pregraphUMC.
Coercion Pred_of_pregraph (f : pregraph) : Pred_Class := [eta Mem_UmMap f].

Definition pg_pts (k : ptr) (v : bin_node) :=
  @UMC.pts ptr_ordType ptr_pred bin_node pregraphUMC k v.

(* baking ptr_pred into the notation *)
Notation "x &-> v" := (@pg_pts x v) (at level 30).

Fact no_null (g : pregraph) :
  null \notin dom g.
Proof.
by apply/negP=>/dom_cond.
Qed.

Definition nodeset := [pcm of fset [ordType of ptr]].

(*Structure bpgraph := BPG {structure : pregraph; marked : nodeset}.*)
*)


Section Shape.

Definition node_shape p (n : graph_node) (s : nodeset) :=
  let: GN ns := n in
  [Pred h | h = p :-> (p \in dom s) \+ (p .+ 1 :-> get_nth ns 0 \+ (p .+ 2 :-> get_nth ns 1 \+ p .+ 3 :-> get_nth ns 2))].

Lemma node_shapeK h1 h2 p n s :
  h1 \In node_shape p n s -> h2 \In node_shape p n s -> h1 = h2.
Proof. by case: n=>/= ns ->->. Qed.

Definition shape (gr : pregraph) (m : nodeset) :=
  IterStar.sepit (assocs gr) (fun '(p,n) => node_shape p n m).

Lemma shapeK h1 h2 gr m :
  h1 \In shape gr m -> h2 \In shape gr m -> h1 = h2.
Proof.
rewrite /shape; elim/um_indf: gr h1 h2=>[||p n gr IH V P] h1 h2 /=.
- by rewrite assocs_undef; move/IterStar.sepit0=>->/IterStar.sepit0->.
- by rewrite assocs0; move/IterStar.sepit0=>->/IterStar.sepit0->.
rewrite assocsPtUn //; last by apply: path_all.
case/IterStar.sepit_cons=>h11[h12][{h1}-> H11 H12].
case/IterStar.sepit_cons=>h21[h22][{h2}-> H21 H22].
by rewrite (node_shapeK H11 H21) (IH _ _ H12 H22).
Qed.

Lemma shapeUn g1 g2 m :
  valid (g1 \+ g2) ->
  shape (g1 \+ g2) m =p shape g1 m # shape g2 m.
Proof.
move=>V h; rewrite /shape.
move: (assocs_perm V)=>H.
by rewrite (sepit_perm _ H) IterStar.sepit_cat.
Qed.

Lemma shapePtUn g p n m :
  valid (p &-> n \+ g) ->
  shape (pts p n \+ g) m =p node_shape p n m # shape g m.
Proof.
move=>V h; apply: iff_trans; first by apply: shapeUn.
rewrite /shape assocsPt.
move: (validL V); rewrite validPt=>->/=; split.
- case=>h1[h2][->]; rewrite IterStar.sepit_cons.
  case=>h11[h12][-> H11]; rewrite IterStar.sepit0=>-> H2; rewrite unitR.
  by exists h11, h2.
case=>h1[h2][-> H1 H2].
exists h1, h2; split=>//.
rewrite IterStar.sepit_cons.
exists h1, Unit; split=>//; first by rewrite unitR.
by rewrite IterStar.sepit0.
Qed.

Lemma shapeMPtUn g p m :
  valid m ->
  p \notin dom m ->
  p \notin dom g ->
  shape g (#p \+ m) =p shape g m.
Proof.
move=>Vm Hm Hg h; rewrite /shape; apply: sepitF; case=>q [ns] /=.
move/In_assocs/In_find=>Hq z.
rewrite !InE /= domPtUn validPtUn /= inE /= Vm Hm /=.
suff: p != q by move/negbTE=>->.
apply/negP=>/eqP E; rewrite E in Hg.
by move/In_findNE: Hg; rewrite Hq.
Qed.

End Shape.

(*
(* graph ops and properties *)
Section Bingraph.

(*
Definition forget : bin_node A -> bin_node unit :=
  fun '(BN l _ r) => BN l tt r.

Definition structure : pregraph A -> pregraph unit :=
  mapv forget.

Lemma dom_structure g : dom (structure g) = dom g.
Proof. by apply: dom_omap_some. Qed.

Lemma structure_dom_eq g1 g2 : structure g1 = structure g2 -> dom g1 =i dom g2.
Proof. by move=>Hs; rewrite -dom_structure Hs dom_structure. Qed.

Lemma valid_structure g : valid (structure g) = valid g.
Proof. by rewrite valid_omap. Qed.

Lemma structurePt p n :
  structure (p &-> n) = p &-> forget n.
Proof.
rewrite /structure omapPt; case: ifP=>// /negbT/negbNE/eqP {p}->.
by symmetry; apply/invalidE; rewrite validPt.
Qed.

Lemma structurePtUn p n g :
  structure (p &-> n \+ g) = p &-> forget n \+ structure g.
Proof.
rewrite {1}/structure omapPtUn /=.
case: ifP=>// /negbT V; symmetry; apply/invalidE.
rewrite !validPtUn in V *.
by rewrite valid_structure dom_structure.
Qed.

Corollary structureUnPt p n g :
  structure (g \+ p &-> n) = structure g \+ p &-> forget n.
Proof. by rewrite joinC structurePtUn joinC. Qed.

Lemma find_structure x g :
  find x (structure g) = ssrfun.omap forget (find x g).
Proof. by rewrite /structure find_omap. Qed.
*)
Definition good_ptr (g : pregraph) p : bool := (p == null) || (p \in dom g).

Lemma good_dom (g1 g2 : pregraph) : dom g1 =i dom g2 -> good_ptr g1 =1 good_ptr g2.
Proof.
by move=>H p; rewrite /good_ptr; case: eqP=>/=.
Qed.

Definition good_graph_b (g : pregraph) : bool :=
  valid g &&
  all (fun '(BN l r) => good_ptr g l && good_ptr g r) (range g).

(*
Lemma good_eq g1 g2 :
  valid g1 = valid g2 -> structure g1 = structure g2 ->
  good_graph_b g1 = good_graph_b g2.
Proof.
rewrite /good_graph_b =>->/[dup] Hs ->; case: (valid g2)=>//=.
apply: eq_all; case=>l _ r; rewrite /good_ptr.
by rewrite -!dom_structure Hs.
Qed.
*)
Definition links (g : pregraph) (x : ptr) : option (seq ptr) :=
  ssrfun.omap (fun '(BN l r) => filter (fun x => x \in dom g) [::l;r]) (find x g).

Definition edge (g : pregraph) x y :=
  oapp (fun 'ys => y \in ys) false (links g x).

Arguments edge g x y : simpl never.

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
rewrite /links.
case Hf: (find x g)=>[[l r]|] //=.
case=><-; split; first by move/find_some: Hf.
rewrite -/(filter (fun x => x \in dom g) [::l;r]) all_filter.
by apply/sub_all/all_predT=>z _ /=; apply: implybb.
Qed.

Corollary edge_dom g x y : edge g x y -> (x \in dom g) * (y \in dom g).
Proof.
rewrite /edge; case E: (links g x)=>[v|]//= Ey.
case/linksT: E=>E1 E2; split=>//.
by move/allP: E2; apply.
Qed.

(*
Lemma find_good g x l r :
  good_graph_b g ->
  find x g = Some (BN l r) ->
  links g x = Some [::l; r].
Proof.
case/andP=>Vg Ha; rewrite /links [filter _]lock =>->/=.
unlock. rewrite mem_filter.
*)

Lemma find_edge g x l r y :
  find x g = Some (BN l r) ->
  edge g x y = (y \in dom g) && (y \in [::l; r]).
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

(*
Definition p_val (p : pred A) (g : pregraph A) : applicative_pred ptr :=
  [pred x | um_preim (p \o bn_val) g x].

(* TODO umpreim_neg ? *)
Lemma pvalNeg p g x :
  x \in dom g ->
  p_val p g x = ~~ p_val (negb \o p) g x.
Proof.
case: dom_find=>// n.
rewrite /p_val /= /um_preim=>-> _ _ /=.
by case: negPn=>// /negP/negbTE.
Qed.

Lemma pvalPtUn p x n g y :
  valid (x &-> n \+ g) ->
  p_val p (x &-> n \+ g) y = ((x == y) && p (bn_val n)) || p_val p g y.
Proof.
move=>V; rewrite /p_val /= umpreimUn //= umpreimPt /=; first by rewrite eq_sym.
by move: V; rewrite validPtUn; case/and3P.
Qed.

Lemma plink_val p g x : p_val p g x = (plink p g x).1.
Proof.
by rewrite /plink /p_val /= /um_preim; case: (find x g)=>//=; case.
Qed.

Corollary pval_dom p g x : p_val p g x -> x \in dom g.
Proof.
apply/contraLR=>/(plinkF p).
by rewrite (surjective_pairing (plink _ _ _)); case; rewrite -plink_val =>/negbT.
Qed.

Lemma plink_conn (p : pred A) g x l r :
  find x (structure g) = Some (BN l tt r) ->
  (plink p g x).2 = filter (fun x => x \in dom g) [::l;r].
Proof.
rewrite find_structure /plink.
by case: (find x g)=>//=; case=>_ a _ [->->].
Qed.

Lemma plink_struct p g1 g2 x :
  x \in dom g1 ->
  structure g1 = structure g2 ->
  (plink p g1 x).2 =i (plink p g2 x).2.
Proof.
move=>Hx Hs y.
have: find x (structure g1) = find x (structure g2) by rewrite Hs.
case E2: (find x (structure g2))=>[[l2 [] r2]|].
- move/(plink_conn p)=>->.
  by rewrite (plink_conn p E2) !mem_filter -!dom_structure Hs.
by move/find_none; rewrite dom_structure Hx.
Qed.
*)

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

(*
Lemma eq_connect0 p g x y : x = y -> p_val p g x -> connect p g x y.
Proof. by move->; apply: connect0. Qed.

Lemma connect1 p g x y : prel p g x y -> p_val p g y -> connect p g x y.
Proof. by move=>/= Hp Hy; apply/connectP; exists [:: y]; rewrite /= Hp Hy. Qed.
*)

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

Lemma connect_links_sub p g x l r :
  find x g = Some (BN l r) ->
  {subset connect p g x <= predU (pred1 x) (predU (connect p g l) (connect p g r))}.
Proof.
move=>Hx y; rewrite !inE.
case/connectP=>xs [Hp {y}-> H].
case: xs Hp H=>[|h xs]/=; first by move=>_ _; rewrite eq_refl.
case/andP; rewrite (find_edge _ Hx) !inE; case/andP=>Hh.
case/orP=>/eqP E; rewrite {h}E in Hh *; move=>Hxs _; case/and3P=>Hxp Hcp Ha.
- suff: connect p g l (last l xs) by move=>-> /=; rewrite orbT.
  by apply/connectP; exists xs; rewrite Hh /= Hcp Ha; split=>//; apply: implybT.
suff: connect p g r (last r xs) by move=>->; rewrite !orbT.
by apply/connectP; exists xs; rewrite Hh /= Hcp Ha; split=>//; apply: implybT.
Qed.

Lemma connect_eq_links p g x l r :
  find x g = Some (BN l r) ->
  x \notin dom p ->
  good_ptr g l ->
  good_ptr g r ->
  connect p g x =i predU (pred1 x) (predU (connect p g l) (connect p g r)).
Proof.
move=>Hx Hd Hl Hr y; apply/iffE; split; first by apply: connect_links_sub.
case/or3P.
- move/eqP=>->; apply: connect0=>//.
  by move/find_some: Hx.
- case/connectP=>xs [Hp {y}-> H] /=; case/andP=>Hl1 Ha; apply/connectP.
  exists (l::xs)=>/=; rewrite Hp Hd Hl1 Ha /= andbT; split=>//.
  rewrite (find_edge _ Hx) inE eq_refl /= andbT.
  by case: {Ha}xs Hp H=>//= ??; case/andP; case/edge_dom.
case/connectP=>xs [Hp {y}-> H] /=; case/andP=>Hl1 Ha; apply/connectP.
exists (r::xs)=>/=; rewrite Hp Hd Hl1 Ha /= andbT; split=>//.
rewrite (find_edge _ Hx) !inE eq_refl /= orbT andbT.
by case: {Ha}xs Hp H=>//= ??; case/andP; case/edge_dom.
Qed.

(*
Definition upd_val (p : ptr) (v : A) (g : pregraph A) : pregraph A :=
  match find p g with
  | Some (BN l _ r) => upd p (BN l v r) g
  | None => undef
  end.

Lemma struct_upd_val p (v : A) g :
  p \in dom g ->
  structure (upd_val p v g) = structure g.
Proof.
rewrite /upd_val; case/um_eta=>[[l a r][-> {2}->]].
by rewrite upd_eta !structurePtUn.
Qed.

Lemma valid_upd_val p (v : A) g :
  p \in dom g -> valid (upd_val p v g) = valid g.
Proof.
rewrite /upd_val=>/[dup]/dom_cond Hp; case/um_eta=>[[l a r][-> H]].
by rewrite validU Hp.
Qed.

Lemma upd_val_eta (g : pregraph A) p (v : A) l r :
  find p (structure g) = Some (BN l tt r) ->
  upd_val p v g = p &-> BN l v r \+ free g p.
Proof.
rewrite find_structure /upd_val => Hs.
case: (find p g) Hs=>[[_ x _]|] // [->->].
by apply: upd_eta.
Qed.

(* TODO generalize to "frame"? *)
Lemma pval_neq (g : pregraph A) p x y :
  valid g ->
  x \in dom g ->
  x != y ->
  p_val p (free g x) y = p_val p g y.
Proof.
move=>Vg + Nxy; case/um_eta=>[[l a r][E H]].
rewrite {2}H pvalPtUn /=; last by rewrite H in Vg.
by rewrite (negbTE Nxy).
Qed.

(* pval_neq baked in *)
Lemma pval_upd_val (g : pregraph A) p (v : A) x y :
  valid g ->
  x \in dom g ->
  p_val p (upd_val x v g) y =
    if x == y then p v else p_val p g y.
Proof.
move=>Vg /[dup] Hx; case/um_eta=>[[l a r][E H]].
have Es : find x (structure g) = Some (BN l tt r) by rewrite find_structure E.
rewrite (upd_val_eta _ Es) pvalPtUn /=; last first.
- by move: Vg; rewrite {1}H !validPtUn.
case: eqP=>/= [{y}<-|/eqP]; last by apply: pval_neq.
case: (p v)=>//=.
by rewrite plink_val plinkF // domF inE eq_refl.
Qed.
*)

End Bingraph.

Section Marking.


Lemma connectMPtUn p m g x cs :
  valid m ->
  p \notin dom m ->
  links g p = Some cs ->
  forall z, z != p ->
             x \in cs -> z \in connect       m  g x ->
  exists2 y, y \in cs & z \in connect (#p \+ m) g y.
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
  exists ch; first by rewrite -(links_edge _ Hc).
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
exists ch; first by rewrite -(links_edge _ Hc).
apply/connectP; exists xs2; split=>//.
- by case/edge_dom: He=>_ ->; exact: implybT.
move: Ha; rewrite -cat_cons all_cat; case/andP=>_ Ha.
apply/allP=>z Hz; rewrite domPtUn inE validPtUn !negb_and negb_or /= negbK Vm (negbTE Npm) /=.
move/allP: Ha=>/(_ _ Hz) ->; rewrite andbT.
move: Hz; rewrite inE; case/orP=>[/eqP->|Hz] //.
by apply/negP=>/eqP E; rewrite E Hz in Nxs2.
Qed.

(* TODO generalize to Un *)
Lemma connectMPtUn2 p m g x :
  valid m ->
  p \notin dom m ->
  forall z, z \in connect (#p \+ m) g x ->
            z \in connect        m  g x.
Proof.
move=>Vm Npm z; case/connectP=>xs [Hp Ez Nxs] Ha.
apply/connectP; exists xs; split=>//.
apply/sub_all/Ha=>q; apply: contra.
rewrite domPtUn inE => ->.
by rewrite orbT andbT validPtUn Vm.
Qed.

Corollary connectMPtUnHas p m g cs :
  valid m ->
  p \notin dom m ->
  links g p = Some cs ->
  forall z, z != p ->
  has (fun x => z \in connect m g x) cs = has (fun x => z \in connect (#p \+ m) g x) cs.
Proof.
move=>Vm Npm Hc z Hzp; apply/iffE; split.
- case/hasP=>x Hx Hz; apply/hasP.
  by apply: (connectMPtUn (x:=x)).
case/hasP=>x Hx /(connectMPtUn2 Vm Npm) Hz.
by apply/hasP; exists x.
Qed.


(*

(* TODO adhoc *)
Lemma connect_upd_true (g : pregraph bool) p l r y :
  valid g ->
  find p (structure g) = Some (BN l tt r) ->
  p != y ->
  (y \in connect negb g l) || (y \in connect negb g r) ->
  let g1 := upd_val p true g in
  (y \in connect negb g1 l) || (y \in connect negb g1 r).
Proof.
move=>Vg Hp Np.
have Hd: p \in dom g by rewrite -dom_structure; apply: (find_some Hp).
case/orP.
- case/connectP=>xs [Hxs Ey Hy].
  (* the difference between g and g1 is only the value of p *)
  (* so connectivity depends on whether it's reachable from l (use cycle lemmas?) *)
  case Hpxs: (p \in l::xs); last first.
  - apply/orP; left; apply/connectP; exists xs; split=>//; last first.
    - by rewrite pval_upd_val // (negbTE Np).

    rewrite (eq_in_path (P:=fun x => (x != p) && (x \in dom g)) (e':=prel negb g)) //.
    - move=>x' y'; rewrite -!topredE /= => /andP [Hx' /um_eta [[vl va vr]][Hdx' ?]] /andP [Hy' Hdy'].
      have Hst : find x' (structure g) = Some (BN vl tt vr) by rewrite find_structure Hdx'.
      rewrite -!plink_val pval_upd_val // eq_sym (negbTE Hx') /=.
      rewrite !(plink_conn negb (l:=vl) (r:=vr)) //; last by rewrite struct_upd_val.
      by rewrite !mem_filter (structure_dom_eq (g2:=g)) // struct_upd_val.
    move/negbT: Hpxs; rewrite inE negb_or; case/andP=>Hpl Hpxs.
    move: (full_path_dom Hxs Ey Hy)=>/=; case/andP=>-> Ha; rewrite andbT.
    apply/andP; split; first by rewrite eq_sym.
    rewrite all_predI Ha andbT; apply/allP=>z Hz.
    by apply/negP=>/eqP Ez; rewrite -Ez Hz in Hpxs.
  (* find the suffix of the path after the last p *)
  case: {-1}_ _ _ / (splitLastP Hpxs) (erefl (l::xs)) =>{Hpxs} xs1 xs2 Hxs2.
  case: xs1=>/=.
  - (* p's left link is a loop, so xs starts with r *)
    case=>Elp Exs; rewrite -{xs2}Exs in Hxs2.
    rewrite Elp in Hxs Ey.
    case: xs Hxs Ey Hxs2 =>/=.
    - by move=>_ Eyp; rewrite Eyp eq_refl in Np.
    move=>r' xs; case/andP; case/andP=>_.
    rewrite (plink_conn negb (l:=l) (r:=r)) // mem_filter; case/andP=>Hr'.
    rewrite !inE; case/orP.
    - by move/eqP=>-> _ _; rewrite Elp eq_refl.
    move/eqP=>E'; rewrite {r'}E' in Hr' *.
    rewrite negb_or=> Hr Ey; case/andP =>Npr Nxs.
    apply/orP; right; apply/connectP; exists xs.
    split=>//; last by rewrite pval_upd_val // (negbTE Np).

    rewrite (eq_in_path (P:=fun x => (x != p) && (x \in dom g)) (e':=prel negb g)) //.
    - move=>x' y'; rewrite -!topredE /= => /andP [Hx' /um_eta [[vl va vr]][Hdx' ?]] /andP [Hy' Hdy'].
      have Hst : find x' (structure g) = Some (BN vl tt vr) by rewrite find_structure Hdx'.
      rewrite -!plink_val pval_upd_val // eq_sym (negbTE Hx') /=.
      rewrite !(plink_conn negb (l:=vl) (r:=vr)) //; last by rewrite struct_upd_val.
      by rewrite !mem_filter (structure_dom_eq (g2:=g)) // struct_upd_val.
    move: (full_path_dom Hr Ey Hy)=>/=; case/andP=>-> Ha; rewrite andbT.
    apply/andP; split; first by rewrite eq_sym.
    rewrite all_predI Ha andbT; apply/allP=>z Hz.
    by apply/negP=>/eqP Ez; rewrite -Ez Hz in Nxs.
  (* xs2 can only start with l or p, this decides the component *)
  move=>_ xs1 [_ Exs]; rewrite {xs}Exs in Hxs Ey.
  case: xs2 Ey Hxs Hxs2 =>/=.
  - by rewrite cats0 last_rcons => Eyp; rewrite Eyp eq_refl in Np.
  move=>h xs2; rewrite cat_path last_cat last_rcons /= => Ey.
  case/and3P=>_; case/andP=>_.
  rewrite (plink_conn negb (l:=l) (r:=r)) // mem_filter; case/andP=>Hh.
  rewrite !inE negb_or; case/orP=>/eqP Eh;
  rewrite {h}Eh in Ey Hh *; move=>Hxs2; case/andP=>Np' Npxs2.
  - apply/orP; left.
    apply/connectP; exists xs2; split=>//; last first.
    - by rewrite pval_upd_val // (negbTE Np).

    rewrite (eq_in_path (P:=fun x => (x != p) && (x \in dom g)) (e':=prel negb g)) //.
    - move=>x' y'; rewrite -!topredE /= => /andP [Hx' /um_eta [[vl va vr]][Hdx' ?]] /andP [Hy' Hdy'].
      have Hst : find x' (structure g) = Some (BN vl tt vr) by rewrite find_structure Hdx'.
      rewrite -!plink_val pval_upd_val // eq_sym (negbTE Hx') /=.
      rewrite !(plink_conn negb (l:=vl) (r:=vr)) //; last by rewrite struct_upd_val.
      by rewrite !mem_filter (structure_dom_eq (g2:=g)) // struct_upd_val.
    move: (full_path_dom Hxs2 Ey Hy)=>/=; case/andP=>-> Ha; rewrite andbT.
    apply/andP; split; first by rewrite eq_sym.
    rewrite all_predI Ha andbT; apply/allP=>z Hz.
    by apply/negP=>/eqP Ez; rewrite -Ez Hz in Npxs2.

  apply/orP; right.
  apply/connectP; exists xs2; split=>//; last first.
  - by rewrite pval_upd_val // (negbTE Np).

  rewrite (eq_in_path (P:=fun x => (x != p) && (x \in dom g)) (e':=prel negb g)) //.
  - move=>x' y'; rewrite -!topredE /= => /andP [Hx' /um_eta [[vl va vr]][Hdx' ?]] /andP [Hy' Hdy'].
    have Hst : find x' (structure g) = Some (BN vl tt vr) by rewrite find_structure Hdx'.
    rewrite -!plink_val pval_upd_val // eq_sym (negbTE Hx') /=.
    rewrite !(plink_conn negb (l:=vl) (r:=vr)) //; last by rewrite struct_upd_val.
    by rewrite !mem_filter (structure_dom_eq (g2:=g)) // struct_upd_val.
  move: (full_path_dom Hxs2 Ey Hy)=>/=; case/andP=>-> Ha; rewrite andbT.
  apply/andP; split; first by rewrite eq_sym.
  rewrite all_predI Ha andbT; apply/allP=>z Hz.
  by apply/negP=>/eqP Ez; rewrite -Ez Hz in Npxs2.

(* TOOO copypaste *)

Admitted.

Definition mark_eq (x : ptr) (g1 g2 : pregraph bool) :=
  forall y, p_val id g2 y = (y \in connect negb g1 x) || p_val id g1 y.

Lemma mark_eq_sub x g1 g2 :
  mark_eq x g1 g2 ->
  subpred (p_val id g1) (p_val id g2).
Proof. by move=>Hm z; move: (Hm z)=>->->; rewrite orbT. Qed.

Lemma mark_eq_neg x g1 g2 :
  dom g1 =i dom g2 ->
  mark_eq x g1 g2 ->
  {in dom g2, forall y, p_val negb g2 y = (y \notin connect negb g1 x) && p_val negb g1 y}.
Proof.
move=>Hd Hm z Hz; move: (Hm z); rewrite pvalNeg //.
move/negbRL; rewrite negb_or=>->; case: (z \notin connect negb g1 x)=>//=.
by rewrite pvalNeg; [rewrite negbK | rewrite Hd].
Qed.

Corollary mark_eq_sub_neg x g1 g2 :
  dom g1 =i dom g2 ->
  mark_eq x g1 g2 ->
  {in dom g2, subpred (p_val negb g2) (p_val negb g1) }.
Proof. by move=>Hd Hm z Hz; rewrite (mark_eq_neg Hd Hm) //; case/andP. Qed.

Definition mark_rel (x : ptr) (g1 g2 : pregraph bool) :=
  structure g1 = structure g2 /\ mark_eq x g1 g2.

*)

End Marking.
*)

Definition markT : Type := forall (p : ptr),
  {(gr : pregraph) (m_o : nodeset)},
  STsep (fun h => [/\ valid m_o, h \In shape gr m_o, good_graph_b gr, n_graph 3 gr & good_ptr gr p],
        [vfun (_ : unit) h => exists m_s,
                  [/\ valid (m_s \+ m_o), h \In shape gr (m_s \+ m_o) & dom m_s =i connect m_o gr p]]).

Program Definition mark : markT :=
  Fix (fun (go : markT) p =>
    Do (if p == null then ret tt
        else v <-- !p;
             if v then ret tt
             else p ::= true;;
                  l <-- !(p.+ 1);
                  m <-- !(p.+ 2);
                  r <-- !(p.+ 3);
                  go l;;
                  go m;;
                  go r)).
Next Obligation.
move=>go p [gr][m_o][] i /= [Vmo Hg Hgg Hg3 Hp]; apply: vrfV=>V; case/orP: Hp.
- move=>/eqP->; rewrite eq_refl; step=>_.
  exists Unit; rewrite unitL; split=>//; rewrite dom0=>z; rewrite in_nil.
  by rewrite connect_notd {z}//; exact: no_null.
move/[dup]/dom_cond/[dup]=>Np /negbTE ->.
case/um_eta; case=>ns [Hp Egr].
case/andP: (Hgg)=>Vg Eg; rewrite Egr in Vg Hg.
case/(shapePtUn _ Vg): (Hg)=>i1[i2][E H1 H2].
rewrite E H1; step; case: ifP=>[Mp|/negbT Mp].
- step=>V1; exists Unit; rewrite unitL {1}Egr dom0; split=>//.
  - by rewrite (shapePtUn _ Vg) /= Mp; vauto.
  by move=>z; rewrite in_nil connect_notp.
do 4!step.
set l := get_nth ns 0.
set m := get_nth ns 1.
set r := get_nth ns 2.
have Hans : all (good_ptr gr) ns.
- move/allP: Eg => /(_ (GN ns)); apply.
  by rewrite {1}Egr rangePtUn inE Vg eq_refl.
have Hgl : good_ptr gr l by apply: (all_good_get _ Hp).
have Hgm : good_ptr gr m by apply: (all_good_get _ Hp).
have Hgr : good_ptr gr r by apply: (all_good_get _ Hp).
apply: [stepE gr, #p \+ m_o]=>//=.
- split=>//; first by rewrite validPtUn Mp /= andbT.
  rewrite Egr; apply/shapePtUn=>//.
  exists (p :-> true \+ (p.+ 1 :-> l \+ (p.+ 2 :-> m \+ p.+ 3 :-> r))), i2; split=>//=.
  - by rewrite InE /= domPtUn /= inE validPtUn /= Vmo Mp eq_refl.
  by apply/shapeMPtUn=>//; rewrite domF inE eq_refl.
move=>_ i3 [m_l][Vml Sml Hml].
apply: [stepE gr, m_l \+ (#p \+ m_o)]=>//= _ i4 [m_m][Vmm Smm Hmm].
apply: [gE gr, m_m \+ (m_l \+ (#p \+ m_o))]=>//= _ i5 [m_r][Vmr Smr Hmr] V5.

exists (m_r \+ (m_m \+ (m_l \+ #p))); rewrite -!joinA; split=>//.

move=>z.
rewrite domUn inE (validX Vmr) /=.
rewrite domUn inE (validX Vmm) /=.
rewrite domUn inE (validX Vml) /=.
rewrite domPt inE /= Hml Hmm Hmr.
rewrite [RHS](@connect_eq_links _ _ _ ns) // eq_sym.
case/boolP: (z == p); first by move=>_; rewrite !orbT.
move=>Hpz; rewrite orbF /=.

rewrite (connectMPtUnHas (p:=p)) // (connectMUnHas (p:=p) (m2:=m_l) (c:=l)) //.

case/orP: Hgl=>[/eqP->|Hgl].
- rewrite !app_predE !(connect_notd _ (no_null gr)) /=.








- split=>//.



a Hp Hgr Vg Hg H1=>/=Hp Hgr Vg Hg H1.
- step=>V1; exists gr; rewrite {1 2}Hgr Vg -H1 -E; do!split=>//.
  move=>y; rewrite orbC; case: (p_val id gr y)=>//=; symmetry; apply/negbTE.
  by rewrite connect_notp // plink_val /plink Hp.
do 3!step.
have Hp' : p_val negb gr p by rewrite plink_val /plink Hp.
set gr0 := p &-> BN l true r \+ free gr p.
have Hs0 : structure gr = structure gr0 by rewrite Hgr /gr0 !structurePtUn.
have V0 : valid gr0 by rewrite !validPtUn in Vg *.
have Hg0 : good_graph_b gr0 by rewrite (good_eq (g2:=gr)) // /gr0 {2}Hgr !validPtUn.
have Hgl0 : good_ptr gr0 l.
- case/andP: Hg0=>_ /allP /(_ (BN l tt r)).
  rewrite structurePtUn rangePtUn inE eq_refl /= andbT.
  rewrite !validPtUn in V0 *; rewrite valid_structure dom_structure V0.
  by move/(_ erefl); case/andP.
apply: [stepE gr0]=>//=; first by split=>//; apply/shapePtUn=>//; vauto.
move=>_ m [gr'][Hm V' [Hs Hmk]].
have Hgg' : good_graph_b gr'.
- rewrite (good_eq (g2:=gr0)) // /gr0 V'.
  by rewrite !validPtUn in V0 *.
have Hgr': good_ptr gr' r.
- case/andP: Hgg' =>_ /allP /(_ (BN l tt r)).
  rewrite -Hs structurePtUn rangePtUn inE eq_refl /= andbT.
  rewrite !validPtUn in V0 *; rewrite valid_structure dom_structure V0.
  by move/(_ erefl); case/andP.
apply: [gE gr']=>//=_ m' [g''][V'' Hm' [Hs' Hmk'] Vm']; exists g''; split=>//.

(* now it's just about marking *)
have Hs'' : structure gr = structure g'' by rewrite Hs0 Hs.
split=>// y.

rewrite Hmk' Hmk.

have -> : p_val id gr0 y = (p==y) || p_val id gr y.
- by rewrite Hgr /gr0 !pvalPtUn // andbT andbF.

case/boolP: (p == y)=> [/eqP {y}<-| Hyp] /=.
- by rewrite !orbT; symmetry; apply/orP; left; apply/connect0.
case/boolP: (p_val id gr y)=>[|Hfy]; first by rewrite !orbT.
rewrite !orbF.

rewrite [RHS](@connect_eq_links _ _ _ _ l false r)=>//; first last.
- by rewrite (good_dom (g2:=gr')) //; apply: structure_dom_eq; rewrite Hs0.
- by rewrite (good_dom (structure_dom_eq Hs0)).
rewrite !inE !app_predE eq_sym (negbTE Hyp) /=.

have Hpeq0: subpred (p_val negb gr0) (p_val negb gr).
- move=>z; rewrite Hgr /gr0 !pvalPtUn //= andbT andbF /= => ->.
  by rewrite orbT.

apply/iffE; split.
- case/orP.
  - move: (Hgr'); rewrite /good_ptr; case/boolP: (r == null)=>/= [/eqP-> _ |_ Hrd].
    - by rewrite connect_notp // plink_val plinkF // no_null.
    have Hpeq: {in dom gr', subpred (p_val negb gr') (p_val negb gr) }.
    - by move=>z Hz /(mark_eq_sub_neg (structure_dom_eq Hs) Hmk Hz)/Hpeq0.
    move/(connect_sub _ Hpeq); rewrite Hs0 Hs app_predE=>/(_ erefl) ->.
    by rewrite orbT.
  move=>Hly; suff: y \in connect negb gr l by move=>->.
  by apply/(connect_sub (g1:=gr0))=>// + _.

have Vg': valid gr by case/andP: Hgg.
have Hps: find p (structure gr) = Some (BN l tt r) by rewrite find_structure Hp.
move/(connect_upd_true (p:=p) Vg' Hps Hyp)=>/=; rewrite (upd_val_eta _ Hps) -/gr0.
case/orP; first by move=>->; rewrite orbT.

case/connectP=>xs [Hxs Ey Hy].

have Hd0: dom gr0 =i dom gr' by apply structure_dom_eq.

case/boolP: (all (fun z => z \notin component negb gr0 l) (r::xs))=>Hpxs.

- (* path doesn't go through the marked component *)
  apply/orP; left.
  apply/connectP.
  exists xs; split=>//; last first.
  - rewrite (mark_eq_neg Hd0 Hmk); last by rewrite -Hd0; apply/pval_dom/Hy.
    rewrite Hy andbT Ey.
    by move/allP: Hpxs; apply; exact: mem_last.

    rewrite (eq_in_path (P:=fun x => (x \notin component negb gr0 l) && (x \in dom gr')) (e':=prel negb gr0)) //.
    - move=>x' y'; rewrite -!topredE /= => /andP [Hx' /[dup] Hdx /um_eta [[vl va vr]][Hdx' ?]] /andP [Hy' Hdy'].
      have Hst : find x' (structure gr') = Some (BN vl tt vr) by rewrite find_structure Hdx'.
      rewrite -!plink_val (mark_eq_neg Hd0 Hmk) // Hx' /=; case: (p_val negb gr0 x')=>//=.
      rewrite !(plink_conn negb (l:=vl) (r:=vr)) //; last by rewrite Hs.
      by rewrite !mem_filter (structure_dom_eq (g2:=gr0)).
    rewrite all_predI Hpxs /=; move: (full_path_dom Hxs Ey Hy)=>/=.
    rewrite Hd0; case: (r \in dom gr')=>//=.
    by apply: sub_all=>z; rewrite Hd0.

apply/orP; right.

(* path goes through the marked component, so y is connected to l *)
rewrite -has_predC (eq_has (a2:=fun z=> z \in component negb gr0 l)) in Hpxs; last by move=>z /=; rewrite negbK.
case: {-1}_ _ _ / (split_find_last Hpxs) (erefl (r::xs))=>{Hpxs} z xs1 xs2 Hz. (* z is the last vertex in marked component, xs2 is the free path *)
rewrite -all_predC (eq_all (a2:=fun z=> z \notin component negb gr0 l)) // => Hxs2 Heq.

apply: (connect_trans (y:=z))=>//.
apply/connectP; exists xs2; split=>//; last first.
- by move: (erefl (last r (r :: xs))); rewrite {1}Heq /= last_cat last_rcons => ->.

case: xs1 Heq=>/=.
- by case=><- <-.
move=>h xs1; case=>? Exs; move: Hxs.
by rewrite Exs cat_path last_rcons; case/andP.
Qed.
