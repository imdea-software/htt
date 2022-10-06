From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype ssrnat seq path.
(* temp*)
From mathcomp Require Import bigop.
From fcsl Require Import options axioms pred prelude seqperm.

From fcsl Require Import pcm unionmap heap autopcm automap.
From HTT Require Import interlude model heapauto.

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
(*
Definition wand (p2 p : Pred U) : Pred U :=
  [Pred h1 | forall h2 h, h = h1 \+ h2 -> h2 \In p2 -> h \In p].
*)
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
(*
Notation "p2 '--#' p" := (wand p2 p)
  (at level 58, right associativity) : rel_scope.
*)
Variant bin_node A := BN of ptr & A & ptr.

Definition bn_get {A} : bin_node A -> ptr * A * ptr :=
  fun '(BN l a r) => (l, a, r).

Definition bn_val {A} : bin_node A -> A :=
  fun '(BN _ a _) => a.

Definition bn_sub {A} : ptr * A * ptr -> bin_node A :=
  fun '(l, a, r) => BN l a r.

Lemma bn_ccl {A : Type} : ssrfun.cancel bn_get (@bn_sub A).
Proof. by case; case. Qed.

Definition binnode_eqMixin {A : eqType} := CanEqMixin (@bn_ccl A).
Canonical binnode_eqType A := Eval hnf in EqType _ (@binnode_eqMixin A).

Notation ptr_pred := (fun x : ptr => x != null).

Module Type PGSig.

Parameter tp : Type -> Type.

Section Params.
Variable A : Type.
Notation tp := (tp A).

Parameter pg_undef : tp.
Parameter defined : tp -> bool.
Parameter empty : tp.
Parameter upd : ptr -> bin_node A -> tp -> tp.
Parameter dom : tp -> seq ptr.
Parameter dom_eq : tp -> tp -> bool.
Parameter assocs : tp -> seq (ptr * bin_node A).
Parameter free : tp -> ptr -> tp.
Parameter find : ptr -> tp -> option (bin_node A).
Parameter union : tp -> tp -> tp.
Parameter empb : tp -> bool.
Parameter undefb : tp -> bool.
Parameter pts : ptr -> bin_node A -> tp.

Parameter from : tp -> @UM.base ptr_ordType ptr_pred (bin_node A).
Parameter to : @UM.base ptr_ordType ptr_pred (bin_node A) -> tp.

Axiom ftE : forall b, from (to b) = b.
Axiom tfE : forall f, to (from f) = f.
Axiom undefE : pg_undef = to (@UM.Undef ptr_ordType ptr_pred (bin_node A)).
Axiom defE : forall f, defined f = UM.valid (from f).
Axiom emptyE : empty = to (@UM.empty ptr_ordType ptr_pred (bin_node A)).
Axiom updE : forall k v f, upd k v f = to (UM.upd k v (from f)).
Axiom domE : forall f, dom f = UM.dom (from f).
Axiom dom_eqE : forall f1 f2, dom_eq f1 f2 = UM.dom_eq (from f1) (from f2).
Axiom assocsE : forall f, assocs f = UM.assocs (from f).
Axiom freeE : forall f k, free f k = to (UM.free (from f) k).
Axiom findE : forall k f, find k f = UM.find k (from f).
Axiom unionE : forall f1 f2, union f1 f2 = to (UM.union (from f1) (from f2)).
Axiom empbE : forall f, empb f = UM.empb (from f).
Axiom undefbE : forall f, undefb f = UM.undefb (from f).
Axiom ptsE : forall k v, pts k v = to (@UM.pts ptr_ordType ptr_pred (bin_node A) k v).

End Params.
End PGSig.

Module PGDef : PGSig.
Section PGDef.
Variable A : Type.

Definition tp : Type := @UM.base ptr_ordType ptr_pred (bin_node A).

Definition pg_undef := @UM.Undef ptr_ordType ptr_pred (bin_node A).
Definition defined f := @UM.valid ptr_ordType ptr_pred (bin_node A) f.
Definition empty := @UM.empty ptr_ordType ptr_pred (bin_node A).
Definition upd k v f := @UM.upd ptr_ordType ptr_pred (bin_node A) k v f.
Definition dom f := @UM.dom ptr_ordType ptr_pred (bin_node A) f.
Definition dom_eq f1 f2 := @UM.dom_eq ptr_ordType ptr_pred (bin_node A) f1 f2.
Definition assocs f := @UM.assocs ptr_ordType ptr_pred (bin_node A) f.
Definition free f k := @UM.free ptr_ordType ptr_pred (bin_node A) f k.
Definition find k f := @UM.find ptr_ordType ptr_pred (bin_node A) k f.
Definition union f1 f2 := @UM.union ptr_ordType ptr_pred (bin_node A) f1 f2.
Definition empb f := @UM.empb ptr_ordType ptr_pred (bin_node A) f.
Definition undefb f := @UM.undefb ptr_ordType ptr_pred (bin_node A) f.
Definition pts k v := @UM.pts ptr_ordType ptr_pred (bin_node A) k v.

Definition from (f : tp) : @UM.base ptr_ordType ptr_pred (bin_node A) := f.
Definition to (b : @UM.base ptr_ordType ptr_pred (bin_node A)) : tp := b.

Lemma ftE b : from (to b) = b. Proof. by []. Qed.
Lemma tfE f : to (from f) = f. Proof. by []. Qed.
Lemma undefE : pg_undef = to (@UM.Undef ptr_ordType ptr_pred (bin_node A)). Proof. by []. Qed.
Lemma defE f : defined f = UM.valid (from f). Proof. by []. Qed.
Lemma emptyE : empty = to (@UM.empty ptr_ordType ptr_pred (bin_node A)). Proof. by []. Qed.
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
Lemma ptsE k v : pts k v = to (@UM.pts ptr_ordType ptr_pred (bin_node A) k v).
Proof. by []. Qed.

End PGDef.
End PGDef.

Notation pregraph := PGDef.tp.

Definition pregraphMixin A :=
  UMCMixin (@PGDef.ftE A) (@PGDef.tfE A) (@PGDef.defE A)
           (@PGDef.undefE A) (@PGDef.emptyE A) (@PGDef.updE A)
           (@PGDef.domE A) (@PGDef.dom_eqE A) (@PGDef.assocsE A)
           (@PGDef.freeE A) (@PGDef.findE A) (@PGDef.unionE A)
           (@PGDef.empbE A) (@PGDef.undefbE A) (@PGDef.ptsE A).

Canonical pregraphUMC A :=
  Eval hnf in UMC (pregraph A) (@pregraphMixin A).

(* we add the canonical projections matching against naked type *)
(* thus, there are two ways to get a PCM for a union map: *)
(* generic one going through union_map_classPCM, and another by going *)
(* through union_mapPCM. Luckily, they produce equal results *)
(* and this is just a matter of convenience *)
(* Ditto for the equality type *)

Definition pregraphPCMMix A := union_map_classPCMMix (pregraphUMC A).
Canonical pregraphPCM A := Eval hnf in PCM (pregraph A) (@pregraphPCMMix A).

Definition pregraphCPCMMix A := union_map_classCPCMMix (pregraphUMC A).
Canonical pregraphCPCM A := Eval hnf in CPCM (pregraph A) (@pregraphCPCMMix A).

Definition pregraphTPCMMix A := union_map_classTPCMMix (pregraphUMC A).
Canonical pregraphTPCM A := Eval hnf in TPCM (pregraph A) (@pregraphTPCMMix A).

Definition pregraph_eqMix (A : eqType) :=
  @union_map_class_eqMix ptr_ordType ptr_pred (binnode_eqType A) _ (@pregraphMixin A).
Canonical pregraph_eqType (A : eqType) :=
  Eval hnf in EqType (pregraph A) (@pregraph_eqMix A).

(* installing the Pred structure for writing x \In h *)
Canonical Structure pregraph_PredType A : PredType (ptr * bin_node A) :=
  Mem_UmMap_PredType (pregraphUMC A).
Coercion Pred_of_pregraph A (f : pregraph A) : Pred_Class := [eta Mem_UmMap f].

Definition pg_pts A (k : ptr) (v : bin_node A) :=
  @UMC.pts ptr_ordType ptr_pred (bin_node A) (@pregraphUMC A) k v.

(* baking ptr_pred into the notation *)
Notation "x &-> v" := (@pg_pts _ x v) (at level 30).

Fact no_null A (g : pregraph A) :
  null \notin dom g.
Proof.
by apply/negP=>/dom_cond.
Qed.

Section Bingraph.
Variable A : Type.

Definition node_shape p (n : bin_node A) :=
  let: BN l a r := n in
  [Pred h | h = p :-> l \+ (p .+ 1 :-> a \+ p .+ 2 :-> r)].

Lemma node_shapeK h1 h2 p n :
  h1 \In node_shape p n -> h2 \In node_shape p n -> h1 = h2.
Proof. by case: n=>/= l a r ->->. Qed.

Definition shape (gr : pregraph A) :=
  IterStar.sepit (assocs gr) (fun '(p,n) => node_shape p n).

Lemma shapeK h1 h2 gr :
  h1 \In shape gr -> h2 \In shape gr -> h1 = h2.
Proof.
rewrite /shape; elim/um_indf: gr h1 h2=>[||p n gr IH V P] h1 h2 /=.
- by rewrite assocs_undef; move/IterStar.sepit0=>->/IterStar.sepit0->.
- by rewrite assocs0; move/IterStar.sepit0=>->/IterStar.sepit0->.
rewrite assocsPtUn //; last by apply: path_all.
case/IterStar.sepit_cons=>h11[h12][{h1}-> H11 H12].
case/IterStar.sepit_cons=>h21[h22][{h2}-> H21 H22].
by rewrite (node_shapeK H11 H21) (IH _ _ H12 H22).
Qed.

Lemma shapeUn g1 g2 :
  valid (g1 \+ g2) ->
  shape (g1 \+ g2) =p shape g1 # shape g2.
Proof.
move=>V h; rewrite /shape.
move: (assocs_perm V)=>H.
by rewrite (sepit_perm _ H) IterStar.sepit_cat.
Qed.

Lemma shapePtUn g p n :
  valid (p &-> n \+ g) ->
  shape (pts p n \+ g) =p node_shape p n # shape g.
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

(*
(* focusing on a node *)
Lemma in_shape g p :
  p \in dom g ->
  forall h, valid h ->
  h \In shape g <-> exists n, h \In node_shape p n # (node_shape p n --# shape g).
Proof.
elim/um_indf: g.
- by rewrite dom_undef.
- by rewrite dom0.
move=>q nq g IH V P; rewrite domPtUn -topredE /= => /andP [_] /orP E h Vh.
rewrite /shape assocsPtUn //; last by apply: path_all.
case: E.
- move/eqP=>E; rewrite {q}E in V P *.
  rewrite IterStar.sepit_cons; split.
  - case=>h1[h2][E H1 H2]; exists nq, h1, h2; split=>// h22 _ -> H22.
    by apply/IterStar.sepit_cons; exists h22, h2; split=>//; rewrite joinC.
  case=>n [h1][h2][E H1 H2]; exists h1, h2; split=>//; rewrite {h}E in Vh.
  move: (H2 h1 (h2 \+ h1) erefl H1)=>/IterStar.sepit_cons [h3][h4][E2 H3 H4].
  move: (node_shapeK H3 H1)=>E3; rewrite {h3 H3}E3 joinC in E2.
  by move: (joinxK Vh E2)=>->.
- move/eqP=>->.

  case=>[{q}<-{nq}<-] h Vh; rewrite /shape IterStar.sepit_cons; split.
  - case=>h1[h2][E H1 H2]; exists h1, h2; split=>// h22 _ -> H22.
    by apply/IterStar.sepit_cons; exists h22, h2; split=>//; rewrite joinC.
  case=>h1[h2][E H1 H2]; exists h1, h2; split=>//; rewrite {h}E in Vh.
  move: (H2 h1 (h2 \+ h1) erefl H1)=>/IterStar.sepit_cons [h3][h4][E2 H3 H4].
  move: (node_shapeK H3 H1)=>E3; rewrite {h3 H3}E3 joinC in E2.
  by move: (joinxK Vh E2)=>->.
move/IH=>{}IH h Vh; rewrite /shape IterStar.sepit_cons; split.
- case=>h1[h2][E H1 /[dup] H2]; rewrite E in Vh.
  case/(IH h2 (validR Vh))=>h3[h4][E2 H3 H4].
  exists h3, (h1 \+ h4); rewrite E E2 joinCA; split=>// h5 _ -> H5.
  move: (node_shapeK H5 H3)=>{h5 H5}->; rewrite IterStar.sepit_cons.
  by exists h1, h2; split=>//; rewrite E2 joinA joinAC.
case=>h1[h2][E H1 H2].
move: (H2 h1 h); rewrite joinC => /(_ E H1).
by rewrite IterStar.sepit_cons; case=>h3[h4][E2 H3 H4]; exists h3, h4.
Qed.


case: n=>p l r V + Hg; case/(in_shape Hg V)=>h1[h2][E H1 _].
by rewrite E H1 in V.
Qed.
*)

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

(*
Definition struct_eq (g1 g2 : pregraph A) : Prop :=
  um_all2 (fun '(BN l1 _ r1) '(BN l2 _ r2) => (l1 == l2) && (r1 == r2)) g1 g2.

Lemma struct_eq_refl g : struct_eq g g.
Proof.
by apply: umall2_refl; case=>l _ r; rewrite !eq_refl.
Qed.
*)
Definition good_ptr (g : pregraph A) p : bool := (p == null) || (p \in dom g).

Lemma good_dom (g1 g2 : pregraph A) : dom g1 =i dom g2 -> good_ptr g1 =1 good_ptr g2.
Proof.
by move=>H p; rewrite /good_ptr; case: eqP=>/=.
Qed.
(*
Lemma good_dom (g1 g2 : pregraph A) p : dom_eq g1 g2 -> good_ptr g1 <-> good_ptr g2.
Proof.
move=>H; rewrite /good_ptr; case: eqP=>//= Hp.
move/domeqP: H =>[_ H].
by rewrite (H p).
Qed.
*)
(*
Definition good_graph (g : pregraph A) : Prop :=
  forall p l a r, find p g = Some (BN l a r) -> good_ptr l g && good_ptr r g.
*)

Definition good_graph_b (g : pregraph A) : bool :=
  valid g &&
  all (fun '(BN l _ r) => good_ptr g l && good_ptr g r) (range (structure g)).

Lemma good_eq g1 g2 :
  valid g1 = valid g2 -> structure g1 = structure g2 ->
  good_graph_b g1 = good_graph_b g2.
Proof.
rewrite /good_graph_b =>->/[dup] Hs ->; case: (valid g2)=>//=.
apply: eq_all; case=>l _ r; rewrite /good_ptr.
by rewrite -!dom_structure Hs.
Qed.

Definition plink (p : pred A) (g : pregraph A) (x : ptr) : bool * seq ptr :=
  match find x g with
  | Some (BN l a r) => (p a, filter (fun x => x \in dom g) [::l;r])
  | None => (false, [::])
  end.

Definition prel (p : pred A) (g : pregraph A) :=
  [rel x y | (plink p g x).1 && (y \in (plink p g x).2)].

Fixpoint dfs (p : pred A) (g : pregraph A) n (v : seq ptr) x :=
  if (x \in v) || ~~ (plink p g x).1 then v else
  if n is n'.+1 then foldl (dfs p g n') (x :: v) (plink p g x).2 else v.

(*
Variant dfs_path (p : pred A) (g : pregraph A) (v : seq ptr) : ptr -> ptr -> Prop :=
  | DfsSame : forall x l a r,
              find x g = Some (BN l a r) -> p a ->
              x \notin v ->
              dfs_path p g v x x
  | DfsPath : forall x y l a r xs,
              path (pred_linked p g) x (rcons xs y) ->
              find y g = Some (BN l a r) -> p a ->
              all (fun z => z \notin v) (x::rcons xs y) ->
              dfs_path p g v x y.

Lemma dfs_pathP p g n x y v :
  size (dom g) <= size v + n ->
  uniq v ->
  {subset v <= dom g} ->
  y \in dom g ->
  y \notin v ->
  reflect (dfs_path p g v x y) (y \in pred_dfs p g n v x).
Proof.
(*
have dfs_id w z: z \notin w -> dfs_path w z z.
  by exists [::]; rewrite ?disjoint_has //= orbF.
*)
elim: n => [|n IHn] /= in x y v * => Hv Uv Sv Hy Ny.
- rewrite addn0 (*. (geq_leqif (subset_leqif_card (subset_predT _))) *) in Hv.
  by case: (uniq_min_size Uv Sv Hv) Ny=>_ /(_ y); rewrite Hy=>->.
case E: (pred_links p g x)=>[px ls].
case/boolP: (x==y).
- move/eqP=>Exy; rewrite {x}Exy in E *.
  move/negbTE: (Ny)=>->/=.
  case: ifP.
  apply: IHn.
have [v_x | not_vx] := ifPn.
  by rewrite (negPf not_vy); right=> [] [p _ _]; rewrite disjoint_has /= v_x.
set v1 := x :: v; set a := g x; have sub_dfs := subsetP (subset_dfs n _ _).
have [-> | neq_yx] := eqVneq y x.
  by rewrite sub_dfs ?mem_head //; left; apply: dfs_id.
apply: (@equivP (exists2 x1, x1 \in a & dfs_path v1 x1 y)); last first.
  split=> {IHn} [[x1 a_x1 [p g_p p_y]] | [p /shortenP[]]].
    rewrite disjoint_has has_sym /= has_sym /= => /norP[_ not_pv].
    by exists (x1 :: p); rewrite /= ?a_x1 // disjoint_has negb_or not_vx.
  case=> [_ _ _ eq_yx | x1 p1 /=]; first by case/eqP: neq_yx.
  case/andP=> a_x1 g_p1 /andP[not_p1x _] /subsetP p_p1 p1y not_pv.
  exists x1 => //; exists p1 => //.
  rewrite disjoint_sym disjoint_cons not_p1x disjoint_sym.
  by move: not_pv; rewrite disjoint_cons => /andP[_ /disjointWl->].
have{neq_yx not_vy}: y \notin v1 by apply/norP.
have{le_v'_n not_vx}: #|T| <= #|v1| + n by rewrite cardU1 not_vx addSnnS.
elim: {x v}a v1 => [|x a IHa] v /= le_v'_n not_vy.
  by rewrite (negPf not_vy); right=> [] [].
set v2 := dfs n v x; have v2v: v \subset v2 := subset_dfs n v [:: x].
have [v2y | not_v2y] := boolP (y \in v2).
  by rewrite sub_dfs //; left; exists x; [apply: mem_head | apply: IHn].
apply: {IHa}(equivP (IHa _ _ not_v2y)).
  by rewrite (leq_trans le_v'_n) // leq_add2r subset_leq_card.
split=> [] [x1 a_x1 [p g_p p_y not_pv]].
  exists x1; [exact: predU1r | exists p => //].
  by rewrite disjoint_sym (disjointWl v2v) // disjoint_sym.
suffices not_p1v2: [disjoint x1 :: p & v2].
  case/predU1P: a_x1 => [def_x1 | ]; last by exists x1; last exists p.
  case/pred0Pn: not_p1v2; exists x; rewrite /= def_x1 mem_head /=.
  suffices not_vx: x \notin v by apply/IHn; last apply: dfs_id.
  by move: not_pv; rewrite disjoint_cons def_x1 => /andP[].
apply: contraR not_v2y => /pred0Pn[x2 /andP[/= p_x2 v2x2]].
case/splitPl: p_x2 p_y g_p not_pv => p0 p2 p0x2.
rewrite last_cat cat_path -cat_cons lastI cat_rcons {}p0x2 => p2y /andP[_ g_p2].
rewrite disjoint_cat disjoint_cons => /and3P[{p0}_ not_vx2 not_p2v].
have{not_vx2 v2x2} [p1 g_p1 p1_x2 not_p1v] := IHn _ _ v le_v'_n not_vx2 v2x2.
apply/IHn=> //; exists (p1 ++ p2); rewrite ?cat_path ?last_cat -?p1_x2 ?g_p1 //.
by rewrite -cat_cons disjoint_cat not_p1v.
Qed.

(*
Definition path_pred (p : pred A) (g : pregraph A) (x y : ptr) : Prop :=
  if x == y then oapp (p \o bn_val) false (find x g) = true
    else exists (xs : seq ptr), path (linked_pred p g) x (rcons xs y).
*)
*)

Lemma plinkF p g x : x \notin dom g -> plink p g x = (false, [::]).
Proof.
by rewrite /plink; move/find_none=>->.
Qed.

Lemma plinkT p g x xs : plink p g x = (true, xs) ->
                        (x \in dom g) * (all (fun z => z \in dom g) xs).
Proof.
rewrite /plink.
case Hf: (find x g)=>[[l a r]|]; last by case.
case=>? <-; split; first by move/find_some: Hf.
rewrite -/(filter (fun x => x \in dom g) [::l;r]) all_filter.
by apply/sub_all/all_predT=>z _ /=; apply: implybb.
Qed.

Lemma subset_dfs p g n v a : {subset v <= foldl (dfs p g n) v a}.
Proof.
elim: n a v => [|n IHn].
- elim=>/=[|h t IH] v; first by move=>?.
  by rewrite if_same.
elim=>/=[|h t IHa v]; first by move=>?.
move=>x Hx; apply: IHa; case: ifP=>//= _.
by apply: IHn; rewrite inE Hx orbT.
Qed.

(* hacky *)
Lemma subset_foldl_dfs_dom p g n v x :
  {subset v <= dom g} ->
  {subset foldl (dfs p g n) v x <= dom g}.
Proof.
elim: n x v=>/=[|n IH].
- by elim=>//= h t IH v; rewrite if_same; apply: IH.
elim=>//=h t IHx v Hv; case: ifP=>/=; first by move=>_; apply: IHx.
move/negbT; rewrite negb_or; case/andP=>_ /negbNE.
case Ep: (plink p g h)=>[px ls] /= Hpx; rewrite {px}Hpx in Ep.
case: (plinkT Ep)=>Hh _.
apply/IHx/IH=>z; rewrite inE; case/orP; last by apply/Hv.
by move/eqP=>{z}->.
Qed.

Corollary subset_dfs_dom p g n v x :
  {subset v <= dom g} ->
  {subset dfs p g n v x <= dom g}.
Proof.
case: n=>/= [|n] H; first by rewrite if_same.
move=>z; case: ifP; first by move=>_ /H.
move/negbT; rewrite negb_or; case/andP=>Hx /negbNE.
case Ep: (plink p g x)=>[px ls] /= Hpx; rewrite {px}Hpx in Ep.
apply: subset_foldl_dfs_dom=>{}z; rewrite inE; case/orP; last by apply/H.
by move/eqP=>{z}->; case: (plinkT Ep).
Qed.

Lemma uniq_dfs_foldl p g n v x : uniq v -> uniq (foldl (dfs p g n) v x).
Proof.
elim: n x v=>/=[|n IH].
- by elim=>//= h t IH v; rewrite if_same; apply: IH.
elim=>//=h t IHx v Hv; case: ifP=>/=; first by move=>_; apply: IHx.
move/negbT; rewrite negb_or; case/andP=>Hx _.
by apply/IHx/IH=>/=; rewrite Hx.
Qed.

Corollary uniq_dfs p g n v x :
  uniq v ->
  uniq (dfs p g n v x).
Proof.
case: n=>/= [|n] H; first by rewrite if_same.
case: ifP=>//.
move/negbT; rewrite negb_or; case/andP=>Hx _.
by apply: uniq_dfs_foldl=>/=; rewrite Hx.
Qed.

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

Inductive dfs_path (p : pred A) g (v : seq ptr) x y : Prop :=
  DfsPath xs of
    path (prel p g) x xs &
    y = last x xs &
    p_val p g y &
    all (fun z => z \notin v) (x::xs).

Lemma dfs_path_id p g v x :
  p_val p g x -> x \notin v -> dfs_path p g v x x.
Proof.
move=>Hx Hv; apply (DfsPath (xs:=[::]))=>//=.
by rewrite andbT.
Qed.

Lemma dfs_pathP p g n x y v :
  size (dom g) <= size v + n ->
  uniq v ->
  {subset v <= dom g} ->
  y \notin v ->
  reflect (dfs_path p g v x y) (y \in dfs p g n v x).
Proof.
case/boolP: (y \in dom g); last first.
- move=>Hy Hv Uv Sv Ny.
  move/contra: (@subset_dfs_dom p _ n _ x Sv y) =>/(_ Hy)/negbTE->.
  by apply: ReflectF; case=>xs _ _; rewrite plink_val (plinkF _ Hy).
elim: n => [|n IHn] /= in x y v * => Hy Hv Uv Sv Ny.
- rewrite addn0 in Hv.
  by case: (uniq_min_size Uv Sv Hv) Ny=>_ /(_ y); rewrite Hy=>->.
case Epl: (plink p g x)=>[px ls] /=.
have [Vx|] := ifPn.
- move/negbTE: (Ny)=>->; apply: ReflectF; case=>/= xs.
  case/orP: Vx; first by move=>->.
  move/negbTE=>Epx; rewrite {px}Epx in Epl.
  case: xs=>/=; last by rewrite Epl.
  by move=>_ ->; rewrite plink_val Epl.
rewrite negb_or; case/andP=>Nx /negbNE Px; rewrite {px}Px in Epl.
set v1 := x :: v; have [-> | Nyx] := eqVneq y x.
- rewrite subset_dfs; last by rewrite inE eq_refl.
  apply: ReflectT; apply: dfs_path_id=>//.
  by rewrite plink_val Epl.
apply: (@equivP (exists2 x1, x1 \in ls & dfs_path p g v1 x1 y)); last first.
- split=> {IHn} [[x1 Hx1 [p1 P1 Ey Py]] | [p1 /shortenP []]] /=.
  - case/andP; rewrite inE negb_or; case/andP =>Ex1 Nx1 Ha1; apply: (DfsPath (xs:=x1::p1))=>//=.
    - by rewrite Epl /= Hx1.
    by rewrite Nx Nx1 /=; apply/sub_all/Ha1=>z; rewrite inE negb_or; case/andP.
  case=>[_ _ _ /= Eyx | x1 xs /=]; first by case/eqP: Nyx.
  rewrite Epl /=. case/andP=>Hx1 Hp1 /and3P [H11 H12 H13] H2 H3 H4 /andP [H5 H6].
  exists x1=>//; apply: (DfsPath (xs:=xs))=>//.
  apply/allP=>z /[dup] Hz /H2; move/allP: H6=>/(_ z) /[apply].
  rewrite !inE negb_or=>->; rewrite andbT; apply/negP=>/eqP Ez.
  by rewrite -Ez Hz in H11.
have{Nyx Ny}: y \notin v1 by apply/norP.
have{Nx Uv}: uniq v1 by rewrite /= Nx.
have{Sv}: {subset v1 <= dom g}.
- move=>z; rewrite inE; case/orP; last by move/Sv.
  by move/eqP=>{z}->; case: (plinkT Epl).
have{Hv}: size (dom g) <= size v1 + n by rewrite addSnnS.
case/plinkT: Epl=>_ Hl.
elim: {x v}ls Hl v1 => /= [_|x a IHa /andP [Ha Hl]] v /= Hv Sv Uv Nv.
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
  by apply: (DfsPath (xs:=p1))=>//; apply/sub_all/Nay=>z; apply/contra/v2v.
suff Nv2: all (fun z => z \notin v2) (x1 :: p1).
- move: Hx1; rewrite inE; case/orP=>[/eqP Ex1|Hx1]; last first.
  - by exists x1=>//; apply: (DfsPath (xs:=p1)).
  rewrite {x1}Ex1 in P1 Ey Nay Nv2.
  exfalso; move: Nv2=>/=; case/andP=>+ _; move/negbTE/negP; apply.
  suff Nx: x \notin v.
  - apply/IHn=>//; apply: dfs_path_id=>//.
    case: {Nay}p1 P1 Ey=>/=[_|??]; first by move=><-.
    by case/andP; case/andP; rewrite plink_val.
  by case/andP: Nay.
apply: contraR Ny2; case/allPn => x2 Hx2 /negbNE Hx2v.
case/splitPl: Hx2 Ey P1 Nay => p0 p2 p0x2.
rewrite last_cat cat_path -cat_cons lastI cat_rcons {}p0x2 => p2y /andP[_ g_p2].
rewrite all_cat /= => /and3P[{p0}_ not_vx2 not_p2v].
have H2d : x2 \in dom g.
- case: {not_p2v}p2 p2y g_p2=>/=[<-|??] // _.
  case Epl: (plink p g x2)=>[uu vv] /=; case/andP; case/andP=>H0.
  by rewrite H0 in Epl; case: (plinkT Epl).
have{not_vx2 Hx2v} [p3 g_p1 p1_x2 V2 not_p1v] := (IHn _ _ v H2d Hv Uv Sv not_vx2 Hx2v).
apply/IHn=>//; exists (p3 ++ p2)=>//.
- by rewrite cat_path g_p1 -p1_x2.
- by rewrite last_cat -p1_x2.
by rewrite -cat_cons all_cat not_p1v.
Qed.

Lemma dfsP p g x y :
  reflect (exists xs, [/\ path (prel p g) x xs, y = last x xs & p_val p g y])
          (y \in dfs p g (size (dom g)) [::] x).
Proof.
apply: (iffP (dfs_pathP _ _ _ _ _ _))=>//.
- by case=>xs P Ey Pv _; exists xs.
case=>xs [P Ey Pv]; apply: (DfsPath (xs:=xs))=>//.
by apply/sub_all/all_predT.
Qed.

Definition connect p g : rel ptr := [rel x y | y \in dfs p g (size (dom g)) [::] x].
Canonical connect_app_pred p g x := ApplicativePred (connect p g x).

Corollary connectP p g x y :
  reflect (exists xs, [/\ path (prel p g) x xs, y = last x xs & p_val p g y])
          (connect p g x y).
Proof. by apply: dfsP. Qed.

Lemma connect_trans p g : transitive (connect p g).
Proof.
move=> x y z /connectP [xs][Hxs -> Hp] /connectP [ys][Hys -> Hp']; apply/connectP.
by exists (xs ++ ys); rewrite cat_path last_cat Hxs.
Qed.

Lemma connect0 p g x : p_val p g x -> connect p g x x.
Proof. by move=>H; apply/connectP; exists [::]. Qed.

Lemma eq_connect0 p g x y : x = y -> p_val p g x -> connect p g x y.
Proof. by move->; apply: connect0. Qed.

Lemma connect1 p g x y : prel p g x y -> p_val p g y -> connect p g x y.
Proof. by move=>/= Hp Hy; apply/connectP; exists [:: y]; rewrite /= Hp Hy. Qed.

Lemma connect_notp p g x :
  ~~ p_val p g x -> connect p g x =i pred0.
Proof.
move=>Hx y; rewrite [RHS]inE; apply/negbTE/connectP.
case=>xs [+ {y}-> +]; case: xs=>/= [_ | h t];
by rewrite -?plink_val (negbTE Hx).
Qed.

Corollary connect_not p g x : x \notin dom g -> connect p g x =i pred0.
Proof.
move=>Hx; apply: connect_notp.
by rewrite plink_val (plinkF _ Hx).
Qed.

Lemma connect_sub p g1 g2 x :
  structure g1 = structure g2 ->
  {in dom g1, subpred (p_val p g1) (p_val p g2) } ->
  subpred (connect p g1 x) (connect p g2 x).
Proof.
move=>Hs Hp z; case/connectP=>xs [Hxs {z}-> H].
apply/connectP; exists xs; split=>//; last first.
- by apply: Hp=>//; apply/pval_dom/H.
elim: xs x Hxs H=>//= h xs IH y.
rewrite -!plink_val; case/andP; case/andP=>H1 H2 H3 H4.
rewrite -andbA; apply/and3P; split; last by apply: IH.
- by apply: Hp=>//; apply/pval_dom/H1.
rewrite -(plink_struct _ _ Hs) //; apply/pval_dom/H1.
Qed.

(*
Lemma connect_lift p g1 g2 x :
  structure g1 = structure g2 ->
  p_val p g1 =1 p_val p g2 ->
  connect p g1 x =i connect p g2 x.
Proof.
have connect_sub p' g3 g4 y:
  structure g3 = structure g4 ->
  p_val p' g3 =1 p_val p' g4 -> subpred (connect p' g3 y) (connect p' g4 y).
 - move=>Hs Hp z; case/connectP=>xs [Hxs {z}-> H].
   apply/connectP; exists xs; split=>//; last by rewrite -Hp.
   elim: xs y Hxs H=>//= h xs IH y.
   rewrite -!plink_val; case/andP; case/andP=>H1 H2 H3 H4.
   rewrite -Hp H1 /= IH // andbT -(plink_struct _ _ Hs) //.
   by apply/pval_dom/H1.
by move=>Hs Hp y; apply/iffE; split; apply: connect_sub.
Qed.
*)

Lemma connect_links_sub (p : pred A) g x l r :
  find x (structure g) = Some (BN l tt r) ->
  {subset connect p g x <= predU (pred1 x) (predU (connect p g l) (connect p g r))}.
Proof.
move=>Hx y; rewrite !inE.
case/connectP=>xs [Hp {y}-> H].
case: xs Hp H=>/=; first by move=>_ _; rewrite eq_refl.
move=>n xs; move: Hx; rewrite /plink find_structure.
case: (find x g)=>[[_ a _]|] // [->->].
case/andP; case/andP=>Hp.
rewrite mem_filter !inE; case/andP=>Hn; case/orP=>/eqP E; rewrite {n}E in Hn *;
move=>Hxs Hpv.
- suff: connect p g l (last l xs) by move=>-> /=; rewrite orbT.
  by apply/connectP; exists xs.
suff: connect p g r (last r xs) by move=>->; rewrite !orbT.
by apply/connectP; exists xs.
Qed.

(*
Lemma connect_links (p : pred A) g x l a r :
  find x g = Some (BN l a r) ->
  {subset connect p g x <= predU (pred1 x) (predU (connect p g l) (connect p g r))}.
Proof.
move=>Hx y; rewrite !inE.
case/connectP=>xs [Hp {y}-> H].
case: xs Hp H=>/=; first by move=>_ _; rewrite eq_refl.
move=>n xs; rewrite /plink Hx; case/andP; case/andP=>Hp.
rewrite mem_filter !inE; case/andP=>Hn; case/orP=>/eqP E; rewrite {n}E in Hn *;
move=>Hxs Hpv.
- suff: connect p g l (last l xs) by move=>-> /=; rewrite orbT.
  by apply/connectP; exists xs.
suff: connect p g r (last r xs) by move=>->; rewrite !orbT.
by apply/connectP; exists xs.
Qed.
*)
Lemma connect_eq_links (p : pred A) g x l a r :
  find x g = Some (BN l a r) ->
  p a ->
  good_ptr g l ->
  good_ptr g r ->
  connect p g x =i predU (pred1 x) (predU (connect p g l) (connect p g r)).
Proof.
move=>Hx Ha Hl Hr y; apply/iffE; split.
- by apply: connect_links_sub; rewrite find_structure Hx.
case/or3P.
- move/eqP=>->; apply: connect0.
  by rewrite plink_val /plink Hx.
- case/connectP=>xs [Hp {y}-> H]; apply/connectP.
  exists (l::xs)=>/=; split=>//; rewrite Hp andbT /plink Hx Ha /=.
  case/orP: Hl.
  - move/eqP=>E; move: Hp H; rewrite E; case: xs=>/=.
    - by move=>_ /umpreim_cond.
    by move=>??; case/andP; case/andP; rewrite -plink_val => /umpreim_cond.
  by move=>->; rewrite inE eq_refl.
case/connectP=>xs [Hp {y}-> H]; apply/connectP.
exists (r::xs)=>/=; split=>//; rewrite Hp andbT /plink Hx Ha /=.
case/orP: Hr.
- move/eqP=>E; move: Hp H; rewrite E; case: xs=>/=.
  - by move=>_ /umpreim_cond.
  by move=>??; case/andP; case/andP; rewrite -plink_val => /umpreim_cond.
by move=>->; case: ifP=>_; rewrite !inE eq_refl // orbT.
Qed.

(*)
Lemma path_connect p g x xs : path (prel p g) x xs -> p_val p g x ->
                              subpred (mem (x :: xs)) (connect p g x).
Proof.
move=>e_p Hx y p_y; case/splitPl: xs / p_y e_p => xs ys <-.
rewrite cat_path => /andP[e_p e_y]; apply/connectP; exists xs; split=>//.
elim: xs x Hx e_p e_y=>//=h xs IH x Hx; case/andP; case/andP=>??? H.
apply: IH=>//.
Qed.
*)

End Bingraph.

(*
Definition torel {A} (g : pregraph A) : ptr -> seq ptr :=
  fun x =>
  match find x g with
  | Some (BN l _ r) => [:: l; r]
  | None => [::]
  end.



Lemma um_eta_t (K : ordType) (C : pred K) (V : Type)
                 (U : union_map_class C V) (k : K) (f : U)  :
        k \in dom f -> sig (fun v => find k f = Some v /\ f = pts k v \+ free f k).
Proof.
case: dom_find=>// v E1 E2 _; exists v; split=>//.
by rewrite {1}E2 -{1}[free f k]unitL updUnR domF inE /= eq_refl ptsU.
Qed.

Lemma pre2fin {A} (g : pregraph A) : good_graph_b g -> seq_sub (dom g) -> seq (seq_sub (dom g)).
Proof.
move=>H [x Hx].
case/um_eta_t: Hx. case=>l a r [E _].
case: (find x g) E=>//; case=>???; case.
*)


Section ExampleCyclic.
Definition p1 := ptr_nat 1.
Definition p2 := ptr_nat 2.
Definition p3 := ptr_nat 3.
Definition p4 := ptr_nat 4.
Definition p5 := ptr_nat 5.
Definition p6 := ptr_nat 6.
Definition p7 := ptr_nat 7.
Definition p8 := ptr_nat 8.

(* https://www.comp.nus.edu.sg/~hobor/Teaching/SW-PhD.pdf#1f *)

Definition ex : pregraph unit :=
  p1 &-> BN p2   tt p3   \+
  p2 &-> BN p4   tt p5   \+
  p3 &-> BN p6   tt p7   \+
  p4 &-> BN null tt null \+
  p5 &-> BN p5   tt p8   \+
  p6 &-> BN p1   tt p8   \+
  p7 &-> BN null tt null \+
  p8 &-> BN p4   tt p7.

End ExampleCyclic.

Section BoolGraph.

(*
Definition good_ptr {A} p (g : graph A) := p == null \/ exists n, (p, n) \In g.

Definition good_graph {A} (g : graph A) :=
  forall p l a r, (p, BN l a r) \In g -> good_ptr l g /\ good_ptr r g.
*)

(*
Inductive un_path : pregraph bool -> ptr -> ptr -> Prop :=
| stop  : forall g p      , un_path g p p
| hopl  : forall g p l r q, (p, BN l false r) \In assocs g -> un_path g l q -> un_path g p q
| hopr  : forall g p l r q, (p, BN l false r) \In assocs g -> un_path g r q -> un_path g p q.

Definition linked_f (g : pregraph bool) (x y : ptr) : bool :=
  match find x g with
  | Some (BN l b r) => ~~b && ((y == l) || (y == r))
  | None => false
  end.

Lemma linked_null g x : ~~ linked_f g null x.
Proof.
by rewrite /linked_f; move: (no_null g)=>/find_none ->.
Qed.
*)

(*
Lemma un_path_b_cat g x y z : un_path_b g x y -> un_path_b g y z -> un_path_b g x z.
Proof.
rewrite /un_path_b; case: eqP; first by move=>->.
move=>Hxy [xs Hxs]; case: eqP.
- by move=><-; move/eqP/negbTE: Hxy=>-> _; exists xs.
move=>Hyz [ys Hys]; case: eqP=>// _.
exists (xs ++ y::ys); rewrite rcons_cat /= -cat1s catA cats1 cat_path.
by rewrite Hxs /= last_rcons.
Qed.

Lemma un_path_null gr x : x \in dom gr -> ~ un_path gr null x.
Proof.
move=>Hx H; case: {1}_ {2}_ {-1}_ / H (erefl gr) (erefl null) (erefl x).
- move=>_ _ _ -> E; rewrite {x}E in Hx.
  by move: (no_null gr); rewrite Hx.
- move=>g p l r _ H _ Eg Ep _; rewrite {g}Eg {p}Ep in H.
  by move: (no_null gr); move/In_assocs/In_dom: H=>->.
move=>g p l r _ H _ Eg Ep _; rewrite {g}Eg {p}Ep in H.
by move: (no_null gr); move/In_assocs/In_dom: H=>->.
Qed.

Lemma un_path_null_b gr x : x \in dom gr -> ~ un_path_b gr null x.
Proof.
move=>Hx; rewrite /un_path_b.
case: eqP.
- move=>E; rewrite -E in Hx.
  by move: (no_null gr); rewrite Hx.
move=>_ []; case=>/=.
- rewrite andbT; apply/negP; exact: linked_null.
by move=>y xs; case/andP=>+ _; apply/negP; exact: linked_null.
Qed.

(* TODO generalize *)
Lemma un_path_frame_b p x y l r g :
  p != null ->
  valid g ->
  p \notin dom g ->
  un_path_b (p &-> BN l true r \+ g) x y -> un_path_b (p &-> BN l false r \+ g) x y.
Proof.
move=>Hp V Hd; rewrite /un_path_b; case: eqP=>// _; case=>xs Hxs; exists xs.
elim: xs x Hxs=>/= [|a xs IH] z.
- rewrite !andbT /linked_f findPtUn2; last by rewrite validPtUn Hp V Hd.
  rewrite findPtUn2; last by rewrite validPtUn Hp V Hd.
  by case: eqP.
case/andP=>Hl /IH ->; rewrite andbT; move: Hl.
rewrite /linked_f findPtUn2; last by rewrite validPtUn Hp V Hd.
rewrite findPtUn2; last by rewrite validPtUn Hp V Hd.
by case: eqP.
Qed.
*)
(*
Lemma un_path_frame p x y l r g :
  x != p ->
  y != p ->
  un_path (p &-> BN l true r \+ g) x y -> un_path (p &-> BN l false r \+ g) x y.
Proof.
move=>Hx Hy H; case: {1}_ {2}_ {-1}_ / H (erefl (p &-> BN l true r \+ g)) (erefl x) (erefl y).
- by move=>_ p' _ Hx' Hy'; rewrite Hx'; constructor.
- move=>g' p' l' r' q H Hp Eg Ex Ey; rewrite {g'}Eg in H Hp; rewrite -{q}Ey in Hp *; rewrite -{p'}Ex in H.
*)

Definition mark_eq (x : ptr) (g1 g2 : pregraph bool) :=
  forall y, p_val id g2 y = (y \in connect negb g1 x) || p_val id g1 y.

Lemma mark_eq_neg x g1 g2 :
  dom g1 =i dom g2 ->
  mark_eq x g1 g2 ->
  {in dom g2, forall y, p_val negb g2 y = (y \notin connect negb g1 x) && p_val negb g1 y}.
Proof.
move=>Hd Hm z Hz; move: (Hm z); rewrite pvalNeg //.
move/negbRL; rewrite negb_or=>->; case: (z \notin connect negb g1 x)=>//=.
by rewrite pvalNeg; [rewrite negbK | rewrite Hd].
Qed.

Corollary mark_eq_sub x g1 g2 :
  dom g1 =i dom g2 ->
  mark_eq x g1 g2 ->
  {in dom g2, subpred (p_val negb g2) (p_val negb g1) }.
Proof. by move=>Hd Hm z Hz; rewrite (mark_eq_neg Hd Hm) //; case/andP. Qed.

Definition mark_rel (x : ptr) (g1 g2 : pregraph bool) :=
  structure g1 = structure g2 /\ mark_eq x g1 g2.

(*
Definition mark_rel (x : ptr) (g1 g2 : pregraph bool) :=
  forall y l r m2, (y, BN l m2 r) \In g2 <->
    exists m1 : bool, (y, BN l m1 r) \In g1 /\
                      if m2 then m1 \/ (~~ m1 /\ un_path_b g1 x y) else ~~ m1.

Lemma mark_linked x a b g1 g2 :
  mark_rel x g1 g2 -> linked_f g2 a b -> linked_f g1 a b.
Proof.
move=>M; rewrite /linked_f.
case H: (find a g2)=>[[l z r]|] //.
move/In_find: H; case/M=>b1 [/In_find ->].
by case: z=>//= ->.
Qed.

Lemma mark_lift a x y g1 g2 :
  mark_rel a g1 g2 ->
  un_path_b g2 x y ->
  un_path_b g1 x y.
Proof.
move=>M; rewrite /un_path_b.
case: eqP=>// _ [xs Hxs]; exists xs.
elim: xs x Hxs=>/= [|z xs IH] x.
- by rewrite !andbT; apply: mark_linked.
by case/andP=>/(mark_linked M)->/=; apply: IH.
Qed.

Lemma mark_trans a b g1 g2 g3 :
  un_path_b g1 a b ->
  mark_rel b g1 g2 -> mark_rel a g2 g3 ->
  mark_rel a g1 g3.
Proof.
move=>P M1 M2 x l r m2.
apply: iff_trans; first by apply: M2.
split.
- case=>m1; case=>/M1; case=>m3 [H1 E1] E2.
  exists m3; split=>// {H1}; case: m3 E1=>/=; case: m2 E2=>//=.
  - case; last by case=>/negbTE->.
    move=>->; case; last by case.
    by move=>_; left.
  - by move/negbTE=>->.
  case.
  - move=>->; case=>//; case=>_ H; right; split=>//.
    by apply/un_path_b_cat/H.
  case=>/negbTE-> H _; right; split=>//.
  apply/(un_path_b_cat P)/(mark_lift M1).
  move: H.
  rewrite /un_path_b.

  first by move=>->.
  case=>/negbTE=>-> H _; right; split=>//.

Lemma mark_good x g1 g2 : mark_rel x g1 g2 -> valid g2 -> good_graph_b g1 -> good_graph_b g2.
Proof.
move=>Hm V2 /andP [V1 H1]; apply/andP; split=>//.
apply/allP; case=>l a r /mem_rangeX; case=>p.
case/(Hm _ _ _ _)=>b [/mem_range Hg1 Hp1].
move/allP: (H1)=>/(_ _ Hg1) /andP [Hl1 Hr1].
apply/andP; split.
- rewrite /good_ptr; case/orP: Hl1=>[->|] //.
  case: eqP=>[->|] /= E; first by move: (no_null g1); rewrite E.
  move/In_domX; case; case=>l' a' r' H'.
  apply/In_domX; exists (BN l' a' r'); apply/Hm.
  by exists a'; split=>//; case: {H'}a'=>//; left.
rewrite /good_ptr; case/orP: Hr1=>[->|] //.
case: eqP=>[->|] /= E; first by move: (no_null g1); rewrite E.
move/In_domX; case; case=>l' a' r' H'.
apply/In_domX; exists (BN l' a' r'); apply/Hm.
by exists a'; split=>//; case: {H'}a'=>//; left.
Qed.
*)
Definition markT : Type := forall (p : ptr),
  {gr : pregraph bool},
  STsep (fun h => [/\ h \In shape gr, good_graph_b gr & good_ptr gr p],
        [vfun (_ : unit) h => exists gr',
                  [/\ h \In shape gr', valid gr' & mark_rel p gr gr']]).

Program Definition mark : markT :=
  Fix (fun (go : markT) p =>
    Do (if p == null then ret tt
        else m <-- !(p.+ 1);
             if m then ret tt
             else l <-- !p;
                  r <-- !(p.+ 2);
                  p.+ 1 ::= true;;
                  go l;;
                  go r)).
Next Obligation.
move=>go p [gr][] i /= [Hg Hgg Hp]; apply: vrfV=>V; case/orP: Hp.
- move=>/eqP->; rewrite eq_refl; step=>_.
  exists gr; do!split=>//; first by case/andP: Hgg.
  move=>x; rewrite connect_not //.
  by apply/find_none/cond_find.
move/[dup]/dom_cond/[dup]=>Np /negbTE ->.
case/um_eta; case=>l a r [Hp Hgr].
case/andP: (Hgg)=>Vg Eg; rewrite Hgr in Vg Hg.
case/(shapePtUn Vg): (Hg)=>i1[i2][E H1 H2].
rewrite E H1; step; case: a Hp Hgr Vg Hg H1=>/=Hp Hgr Vg Hg H1.
- step=>V1; exists gr; rewrite {1 2}Hgr Vg -H1 -E; do!split=>//.
  move=>y; rewrite orbC; case: (p_val id gr y)=>//=; symmetry; apply/negbTE.
  by rewrite connect_notp // plink_val /plink Hp.
have Hp' : p_val negb gr p by rewrite plink_val /plink Hp.
do 3!step.
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
have Hs'' : structure gr = structure g'' by rewrite Hs0 Hs.
split=>// y.

rewrite Hmk' Hmk {2}/gr0 {3}Hgr !pvalPtUn //= andbT andbF /=.
case/boolP: (p == y).
- move/eqP=>{y}<-; rewrite !orbT.
  suff: (p \in connect negb gr p) by move=>->.
  by apply/connect0.
move=>Hyp /=; case/boolP: (p_val id (free gr p) y); first by rewrite !orbT.
move=>Hfy; rewrite !orbF.

have Hpeq0: subpred (p_val negb gr0) (p_val negb gr).
- move=>z; rewrite Hgr /gr0 !pvalPtUn //= andbT andbF /= => ->.
  by rewrite orbT.

apply/iffE; split.
- case/orP.
  - move: (Hgr'); rewrite /good_ptr; case/boolP: (r == null)=>/= [/eqP-> _ |_ Hrd].
    - by rewrite connect_notp // plink_val plinkF // no_null.
    have Hpeq: {in dom gr', subpred (p_val negb gr') (p_val negb gr) }.
    - by move=>z Hz /(mark_eq_sub (structure_dom_eq Hs) Hmk Hz)/Hpeq0.
    move/(connect_sub _ Hpeq); rewrite Hs0 Hs app_predE=>/(_ erefl) Hry.
    rewrite (@connect_eq_links _ _ _ _ l false r)=>//.
    - by rewrite !inE !app_predE Hry !orbT.
    by rewrite (good_dom (structure_dom_eq Hs0)).
    by rewrite (good_dom (g2:=gr')) //; apply: structure_dom_eq; rewrite Hs0.
  move=>Hly; have {}Hly: y \in connect negb gr l.
  - by apply/(connect_sub (g1:=gr0))=>// + _.
  rewrite (@connect_eq_links _ _ _ _ l false r)=>//.
  - by rewrite !inE !app_predE Hly !orbT.
  by rewrite (good_dom (structure_dom_eq Hs0)).
  by rewrite (good_dom (g2:=gr')) //; apply: structure_dom_eq; rewrite Hs0.

move/(@connect_links_sub _ _ _ _ l r).
rewrite find_structure Hp /= !inE !app_predE => /(_ erefl).
rewrite eq_sym (negbTE Hyp) /=; case/orP.
- move=>Hly; apply/orP; right.

rewrite /mark_eq in Hmk Hmk'.





(*
    case/connectP=>xs [Hpx Ey Hy].
    apply/connectP; exists (r::xs)=>/=; split=>//.
    - rewrite -plink_val Hp' /= (plink_conn negb (l:=l) (r:=r)); last by rewrite find_structure Hp.
      rewrite mem_filter !inE eq_refl orbT andbT -dom_structure Hs0 Hs dom_structure Hrd /=.
      apply/sub_path/Hpx=>x' y'.
      case/posnP: (size xs); first by move/eqP/nilP=>->.
      move=>Hsz; apply/pathP=>/=.


case/boolP: (y \in connect negb gr p).
- have Hcon: find p (structure gr) = Some (BN l tt r) by rewrite find_structure Hp'.
  move/[dup]=>Hy /(connect_links Hcon); rewrite !inE eq_sym (negbTE Hyp) /=.
  case/orP.
  - Print right_transitive.

    case/connectP=>xs [Hp -> H]; apply/orP; right.
    apply/connectP; exists xs; split=>//.


case/or3P.
- (* we're looking at p, we know it's unset in gr *)
  move/eqP=>{z}->; apply/orP; left.
  apply: connect0; rewrite Hgr' /p_val umpreimUn // inE.
  by apply/orP; left; rewrite umpreimPt //= eq_refl.
- move=>Hz; have: connect id gr' l z.
  - case/connectP: Hz=>xs [Hp {z}-> H]; apply/connectP.
move=>n0 xs.
rewrite -plink_val (@plink_conn _ _ _ _ true l r); last first.
- apply/In_find.
*)
(*
move=>y0 l0 r0 b2; apply: iff_trans; first by apply: Hmk'.
split.
- case=>b1 [Hb1 Eb1].
  move/Hmk: Hb1; case=>b3 [Hb3 Eb3].
  case/(InPtUnEN _ Vg'): Hb3.
  - case=>E0 {l0}->E3' {r0}->; rewrite {y0}E0 in Eb1 Eb3 *; rewrite {b3}E3' /= in Eb3.
    case: b1 Eb1 Eb3=>//=; case: b2=>//= _ _.
    exists false; split; first by rewrite Hgr'; apply: InPtUnL.
    by right; split=>//; rewrite /un_path_b eq_refl.
  move=>[H0 /= Hn0]; exists b3; split.
  - by rewrite Hgr'; apply/InPtUnE=>//; right.
  case: b1 Eb1 Eb3=>/=; case: b2=>//=.
  - move=>_; case; first by move=>?; left.
    case=>/negbTE Eb3; rewrite {b3}Eb3 in H0 *; move=>Hup; right; split=>//.
    have{Hup}: un_path_b gr l y0.
    - rewrite Hgr'; apply: un_path_frame_b=>//.
      - by move/validR: Vg.
      by rewrite domF -topredE /= eq_refl.
    rewrite /un_path_b; move/negbTE: Hn0; rewrite eq_sym=>->.
    case: eqP.
    - by move=><- _; exists [::]=>/=; rewrite andbT /linked_f Hp' eq_refl.
    by move=>_ [xs Hpu]; exists (l::xs)=>/=; rewrite Hpu andbT /linked_f Hp' eq_refl.
  case=>//; case=>_ Hup /negbTE Eb3; rewrite {b3}Eb3 /= in H0 *; right; split=>//.
  move: Hup; rewrite /un_path_b; move/negbTE: Hn0; rewrite eq_sym=>->.
  case: eqP.
  - by move=><- _; exists [::]=>/=; rewrite andbT /linked_f Hp' eq_refl orbT.
  move=>_ [xs Hpu]; exists (l::xs)=>/=; apply/andP; split.
  - by rewrite /linked_f Hp' eq_refl.
  elim: xs Hpu=>/=.
  - rewrite !andbT /linked_f.
*)

(*
have Hpm : mark_rel p gr gr'.
- move=>y0 l0 r0 b2; apply: iff_trans; first by apply: Hmk.
  split.
  - case=>b1 [H3 E3].
    case/(InPtUnEN _ Vg'): H3.
    - case=>E0 {l0}->E3' {r0}->; rewrite {y0}E0 in E3 *; rewrite {b1}E3' /= in E3.
      exists false; split; first by rewrite Hgr'; apply: InPtUnL.
      case: b2 E3=>//=; case; last by case.
      by move=>_; right; split=>//; rewrite /un_path_b eq_refl.
    move=>[H0 /= Hn0]; exists b1; split.
    - by rewrite Hgr'; apply/InPtUnE=>//; right.
    case: b2 E3=>//.
    case; first by move=>E3; left.
    case=>/negbTE Eb1; rewrite {b1}Eb1 /= in H0 *; move=>Hl; right; split=>//.
    have: un_path_b gr l y0.
    - rewrite Hgr'; apply: un_path_frame_b=>//.
      - by move/validR: Vg.
      by rewrite domF -topredE /= eq_refl.
    rewrite /un_path_b; move/negbTE: Hn0; rewrite eq_sym=>->.
    case: eqP.
    - by move=><- _; exists [::]=>/=; rewrite andbT /linked_f Hp' eq_refl.
    by move=>_ [xs Hpu]; exists (l::xs)=>/=; rewrite Hpu andbT /linked_f Hp' eq_refl.
  admit.

have Hpr : mark_rel p gr' g''.
- move=>y0 l0 r0 b2; apply: iff_trans; first by apply: Hmk'.

  case=>b1 [H3 E3].

  case E0: (y0 == p).
  - move/eqP: E0=>{y0}->; case=>/In_find; rewrite Hp'; case=>{l0}<-{b1}<-{r0}<-/= _.
    exists true.
    case: b2=>/=.
   case exists b1; split.


    move/un_path_frame_b: Hl.
    rewrite Hgr'; apply/un_path_frame_b=>//. apply: (hopl (l:=l) (r:=r)).
      - by apply/In_assocs/InPtUnE=>//; left.

rewrite /mark_rel in Hmk Hmk' *; move=>y0 l0 r0 b2.
apply: iff_trans; first by apply: Hmk'.
split.
- case=>b1 [/Hmk][b3][H3 E3 E2].
  case/(InPtUnEN _ Vg'): H3.
  - case=>E0 {l0}->E3' {r0}->; rewrite {y0}E0 in E2 E3 *; rewrite {b3}E3' in E3.
    exists false; split; first by rewrite Hgr'; apply: InPtUnL.
    by case: b2 E2=>// _; right; constructor.
  move=>[H0 /= Hn0]; exists b3; split.
  - by rewrite Hgr'; apply/(InPtUnE)=>//; right.
  case: b2 E2; last by move/negbTE=>Eb1; rewrite Eb1 in E3.
  case.
  - move=>Eb1; rewrite Eb1 in E3; case: E3; first by move=>E3; left.
    move=>Hpu; right; rewrite Hgr'; apply: (hopl (l:=l) (r:=r)).
    - by apply/In_assocs/InPtUnE=>//; left.

    /mem_rangeX.


    =>/=. first last.
  - by case: (Hgr _ _ _ _ H).


move=>H; move: (Hg); case/(in_shape H V)=>h1[h2][E H1 H2].
rewrite E H1; step; case: m H H1 H2=>/=H H1 H2.
- step=>V1; exists gr; split.
  - by move: Hg; rewrite E H1.
  move=>y l' r' m2; split.
  - by move=>Hm; exists m2; split=>//; case: m2 Hm=>// ?; left.
  case=>m1 [Hy]; case: m2; last by move/negbTE => Em; rewrite Em in Hy.
  case; first by move => Em; rewrite Em in Hy.
  (* TODO graphs should really be PCMs so that we get `p :-> _ true _` vs `p :-> _ false _` contradiction here  *)
  admit.
do 3!step; apply: [stepE gr]=>//=.
- split; first last.
  - by case: (Hgr _ _ _ _ H).




move=>go p [tn][gn][] i /= [Hg Ht]; case: eqP Ht=>[{p}->|/eqP Ep] Ht.
- by step=>V; rewrite (tree_in_graph_null Ht V).
apply: vrfV=>Vi.
case: (tree_in_graph_nonnull Ep Ht)=>x[tl][pl][tr][pr][-> I Hl Hr].
move: (Hg); case/(in_shape I Vi)=>i1[i2][Ei Hi1 Hi2]; rewrite Ei Hi1.
do 3!step.
apply: [stepE tl, gn]=>//=; first by split=>//; rewrite -Hi1 -Ei.
move=>_ m [/eqP -> Hm].
rewrite (shapeK Hm Hg)=>{m Hm}.
by apply: [stepE tr, gn]=>//=_ m [/eqP -> Hm]; step.
Qed.
*)

End BoolGraph.